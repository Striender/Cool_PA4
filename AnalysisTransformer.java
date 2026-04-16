
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.Chain;
import soot.tagkit.*;

import java.util.*;

public class AnalysisTransformer extends SceneTransformer {

    static CallGraph cg;
    static Map<SootMethod, MethodSummary> methodSummaries = new HashMap<>();
    static Map<String, List<String>> redundantLoadResults = new TreeMap<>();

    private int getLine(Unit u) {
        for (Tag t : u.getTags()) {
            if (t instanceof SourceLnPosTag) {
                return ((SourceLnPosTag) t).startLn();
            }
        }
        for (Tag t : u.getTags()) {
            if (t instanceof LineNumberTag) {
                return ((LineNumberTag) t).getLineNumber();
            }
        }
        return u.getJavaSourceStartLineNumber();
    }

    static class State {

        Map<Local, Set<String>> stack = new HashMap<>();
        Map<String, Map<String, Set<String>>> heap = new HashMap<>();

        State() {
        }

        State(State other) {
            for (Local l : other.stack.keySet()) {
                stack.put(l, new HashSet<>(other.stack.get(l)));
            }
            for (String obj : other.heap.keySet()) {
                Map<String, Set<String>> fields = new HashMap<>();
                for (Map.Entry<String, Set<String>> e : other.heap.get(obj).entrySet()) {
                    fields.put(e.getKey(), new HashSet<>(e.getValue()));
                }
                heap.put(obj, fields);
            }
        }

        public boolean equals(Object o) {
            if (!(o instanceof State)) {
                return false;
            }
            State other = (State) o;
            return stack.equals(other.stack) && heap.equals(other.heap);
        }
    }

    static class MethodSummary {

        Set<FieldWriteEffect> fieldWrites = new HashSet<>();

        MethodSummary() {
        }

        MethodSummary(MethodSummary other) {
            fieldWrites = new HashSet<>(other.fieldWrites);
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof MethodSummary)) {
                return false;
            }
            MethodSummary other = (MethodSummary) o;
            return fieldWrites.equals(other.fieldWrites);
        }
    }

    static class FieldWriteEffect {

        String baseRole;
        String field;
        String valueRole;

        FieldWriteEffect(String baseRole, String field, String valueRole) {
            this.baseRole = baseRole;
            this.field = field;
            this.valueRole = valueRole;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof FieldWriteEffect)) {
                return false;
            }
            FieldWriteEffect other = (FieldWriteEffect) o;
            return Objects.equals(baseRole, other.baseRole)
                    && Objects.equals(field, other.field)
                    && Objects.equals(valueRole, other.valueRole);
        }

        @Override
        public int hashCode() {
            return Objects.hash(baseRole, field, valueRole);
        }
    }

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        cg = Scene.v().getCallGraph();

        List<SootMethod> methods = new ArrayList<>();
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod m : sc.getMethods()) {
                if (!m.isConcrete()) {
                    continue;
                }
                if (m.getName().equals("<clinit>")) {
                    continue;
                }

                methods.add(m);
                methodSummaries.put(m, new MethodSummary());
            }
        }

        // PASS 1: position-sensitive method summaries
        boolean changed;
        do {
            changed = false;
            for (SootMethod m : methods) {
                MethodSummary summary = computeMethodSummary(m);
                if (!summary.equals(methodSummaries.get(m))) {
                    methodSummaries.put(m, summary);
                    changed = true;
                }
            }
        } while (changed);

        // PASS 2: Analysis + Redundant Load Elimination
        for (SootMethod m : methods) {
            analyze(m.retrieveActiveBody());
        }

        printRedundantLoadResults();
    }

    private MethodSummary computeMethodSummary(SootMethod m) {

        Body body = m.retrieveActiveBody();
        BriefUnitGraph cfg = new BriefUnitGraph(body);
        Chain<Unit> units = body.getUnits();

        Map<Unit, State> IN = new HashMap<>();
        Map<Unit, State> OUT = new HashMap<>();

        for (Unit u : units) {
            IN.put(u, new State());
            OUT.put(u, new State());
        }

        MethodSummary summary = new MethodSummary();

        State entry = new State();
        if (!m.isStatic()) {
            entry.stack.put(body.getThisLocal(), new HashSet<>(Collections.singleton("THIS")));
        }
        List<Local> params = body.getParameterLocals();
        for (int i = 0; i < params.size(); i++) {
            entry.stack.put(params.get(i), new HashSet<>(Collections.singleton("ARG_" + i)));
        }

        Queue<Unit> worklist = new LinkedList<>(units);

        while (!worklist.isEmpty()) {
            Unit u = worklist.poll();

            State in = merge(u, cfg, OUT, entry);
            IN.put(u, in);

            updateSummary(summary, u, in);

            State out = transferSummary(u, in);

            if (!out.equals(OUT.get(u))) {
                OUT.put(u, out);
                worklist.addAll(cfg.getSuccsOf(u));
            }
        }

        return summary;
    }

    private void analyze(Body body) {

        BriefUnitGraph cfg = new BriefUnitGraph(body);
        Chain<Unit> units = body.getUnits();

        Map<Unit, State> IN = new HashMap<>();
        Map<Unit, State> OUT = new HashMap<>();

        for (Unit u : units) {
            IN.put(u, new State());
            OUT.put(u, new State());
        }

        State entry = new State();
        if (!body.getMethod().isStatic()) {
            entry.stack.put(body.getThisLocal(), new HashSet<>(Collections.singleton("THIS")));
        }
        List<Local> params = body.getParameterLocals();
        for (int i = 0; i < params.size(); i++) {
            entry.stack.put(params.get(i), new HashSet<>(Collections.singleton("ARG_" + i)));
        }

        Queue<Unit> worklist = new LinkedList<>(units);

        while (!worklist.isEmpty()) {

            Unit u = worklist.poll();

            State in = merge(u, cfg, OUT, entry);
            IN.put(u, in);

            State out = transfer(u, in);

            if (!out.equals(OUT.get(u))) {
                OUT.put(u, out);
                worklist.addAll(cfg.getSuccsOf(u));
            }
        }

        checkRedundantLoads(body, IN, OUT, cfg);
    }

    private State merge(Unit u, BriefUnitGraph cfg, Map<Unit, State> OUT) {
        return merge(u, cfg, OUT, new State());
    }

    private State merge(Unit u, BriefUnitGraph cfg, Map<Unit, State> OUT, State entry) {

        List<Unit> preds = cfg.getPredsOf(u);
        if (preds.isEmpty()) {
            return new State(entry);
        }

        State merged = new State(OUT.get(preds.get(0)));

        for (int i = 1; i < preds.size(); i++) {

            State s = OUT.get(preds.get(i));

            for (Local l : s.stack.keySet()) {
                merged.stack
                        .computeIfAbsent(l, k -> new HashSet<>())
                        .addAll(s.stack.get(l));
            }

            mergeHeaps(merged.heap, s.heap);
        }

        return merged;
    }

    private void mergeHeaps(Map<String, Map<String, Set<String>>> dst, Map<String, Map<String, Set<String>>> src) {
        for (Map.Entry<String, Map<String, Set<String>>> objEntry : src.entrySet()) {
            Map<String, Set<String>> fields = dst.computeIfAbsent(objEntry.getKey(), k -> new HashMap<>());
            for (Map.Entry<String, Set<String>> fieldEntry : objEntry.getValue().entrySet()) {
                fields.computeIfAbsent(fieldEntry.getKey(), k -> new HashSet<>()).addAll(fieldEntry.getValue());
            }
        }
    }





    private String fieldName(Value v) {
        if (v instanceof InstanceFieldRef) {
            return ((InstanceFieldRef) v).getField().getName();
        }
        if (v instanceof StaticFieldRef) {
            return ((StaticFieldRef) v).getField().getName();
        }
        return null;
    }

    private Set<String> loadField(State in, Set<String> bases, String field) {
        Set<String> result = new HashSet<>();
        if (bases == null || field == null) {
            return result;
        }

        for (String base : bases) {
            result.addAll(
                    in.heap.getOrDefault(base, Collections.emptyMap())
                            .getOrDefault(field, Collections.emptySet())
            );
        }
        return result;
    }

    private Set<String> abstractValuesOf(State in, Value value, Unit u) {
        if (value instanceof Local) {
            return new HashSet<>(in.stack.getOrDefault((Local) value, Collections.emptySet()));
        }
        if (value instanceof CastExpr) {
            return abstractValuesOf(in, ((CastExpr) value).getOp(), u);
        }
        if (value instanceof InstanceFieldRef
                && ((InstanceFieldRef) value).getBase() instanceof Local) {
            Local base = (Local) ((InstanceFieldRef) value).getBase();
            return loadField(in, in.stack.get(base), fieldName(value));
        }
        if (value instanceof NewExpr) {
            return new HashSet<>(Collections.singleton("0_" + getLine(u)));
        }
        if (value instanceof Constant) {
            return new HashSet<>(Collections.singleton("CONST:" + value.getType() + ":" + value));
        }
        return new HashSet<>();
    }

    private void storeField(State out, Set<String> bases, String field, Set<String> values) {
        if (bases == null || field == null) {
            return;
        }

        boolean strongUpdate = bases.size() == 1;
        for (String base : bases) {
            Map<String, Set<String>> fields
                    = out.heap.computeIfAbsent(base, k -> new HashMap<>());
            if (strongUpdate) {
                fields.put(field, new HashSet<>(values));
            } else {
                fields.computeIfAbsent(field, k -> new HashSet<>()).addAll(values);
            }
        }
    }

    private Set<String> actualObjectsForRole(InvokeExpr expr, State in, String role) {
        if (role == null) {
            return Collections.emptySet();
        }

        if (role.equals("THIS") && expr instanceof InstanceInvokeExpr) {
            Value base = ((InstanceInvokeExpr) expr).getBase();
            if (base instanceof Local) {
                return in.stack.getOrDefault((Local) base, Collections.emptySet());
            }
        } else if (role.startsWith("ARG_")) {
            int index = Integer.parseInt(role.substring(4));
            if (index < expr.getArgs().size() && expr.getArg(index) instanceof Local) {
                return in.stack.getOrDefault((Local) expr.getArg(index), Collections.emptySet());
            }
        }

        return Collections.emptySet();
    }

    private void applyCallEffects(State out, State in, InvokeExpr expr, MethodSummary summary) {
        for (FieldWriteEffect effect : summary.fieldWrites) {
            Set<String> bases = actualObjectsForRole(expr, in, effect.baseRole);
            Set<String> values = actualObjectsForRole(expr, in, effect.valueRole);
            storeField(out, bases, effect.field, values);
        }
    }

    private State transferSummary(Unit u, State in) {

        State out = new State(in);
        if (!(u instanceof AssignStmt)) {
            return out;
        }

        AssignStmt stmt = (AssignStmt) u;
        Value left = stmt.getLeftOp();
        Value right = stmt.getRightOp();

        if (left instanceof Local) {
            if (right instanceof Local) {
                Set<String> rhs = in.stack.getOrDefault(right, Collections.emptySet());
                out.stack.put((Local) left, new HashSet<>(rhs));
            } else if (right instanceof InstanceFieldRef
                    && ((InstanceFieldRef) right).getBase() instanceof Local) {
                Local base = (Local) ((InstanceFieldRef) right).getBase();
                out.stack.put((Local) left,
                        loadField(in, in.stack.get(base), fieldName(right)));
            } else if (right instanceof CastExpr && ((CastExpr) right).getOp() instanceof Local) {
                Local src = (Local) ((CastExpr) right).getOp();
                Set<String> rhs = in.stack.getOrDefault(src, Collections.emptySet());
                out.stack.put((Local) left, new HashSet<>(rhs));
            } else {
                out.stack.remove((Local) left);
            }
        } else if (left instanceof InstanceFieldRef && ((InstanceFieldRef) left).getBase() instanceof Local) {
            Local base = (Local) ((InstanceFieldRef) left).getBase();
            Set<String> rhs = Collections.emptySet();

            if (right instanceof Local) {
                rhs = in.stack.getOrDefault((Local) right, Collections.emptySet());
            } else if (right instanceof NewExpr) {
                rhs = Collections.singleton("ALLOC_" + getLine(u));
            }

            storeField(out, in.stack.get(base), fieldName(left), rhs);
        }

        return out;
    }

    private void updateSummary(MethodSummary summary, Unit u, State in) {

        if (!(u instanceof Stmt)) {
            return;
        }
        Stmt stmt = (Stmt) u;
        int line = getLine(u);

        if (stmt instanceof AssignStmt) {
            Value left = ((AssignStmt) stmt).getLeftOp();
            Value right = ((AssignStmt) stmt).getRightOp();

            if (left instanceof InstanceFieldRef && ((InstanceFieldRef) left).getBase() instanceof Local) {
                Set<String> baseRoles = in.stack.get((Local) ((InstanceFieldRef) left).getBase());
                if (right instanceof Local) {
                    addFieldWriteEffects(summary, baseRoles, fieldName(left),
                            in.stack.get((Local) right));
                }
            }
        }
    }

    private void addFieldWriteEffects(MethodSummary summary, Set<String> baseRoles,
            String field, Set<String> valueRoles) {
        if (baseRoles == null || valueRoles == null || field == null) {
            return;
        }
        for (String baseRole : baseRoles) {
            if (!(baseRole.equals("THIS") || baseRole.startsWith("ARG_"))) {
                continue;
            }
            for (String valueRole : valueRoles) {
                if (valueRole.equals("THIS") || valueRole.startsWith("ARG_")) {
                    summary.fieldWrites.add(new FieldWriteEffect(baseRole, field, valueRole));
                }
            }
        }
    }

    private Set<SootMethod> resolveTargets(Stmt stmt) {
        Set<SootMethod> targets = new HashSet<>();
        Iterator<Edge> edges = cg.edgesOutOf(stmt);
        while (edges.hasNext()) {
            SootMethod target = edges.next().tgt();
            if (target.getDeclaringClass().isApplicationClass()) {
                targets.add(target);
            }
        }
        return targets;
    }

    private State transfer(Unit u, State in) {

        State out = new State(in);
        if (u instanceof AssignStmt) {
            AssignStmt stmt = (AssignStmt) u;
            Value left = stmt.getLeftOp();
            Value right = stmt.getRightOp();

            int line = getLine(u);

            // Allocation
            if (right instanceof NewExpr && left instanceof Local) {

                String obj = "0_" + line;

                out.stack.put((Local) left,
                        new HashSet<>(Arrays.asList(obj)));
            } else if (right instanceof NewExpr
                    && left instanceof InstanceFieldRef
                    && ((InstanceFieldRef) left).getBase() instanceof Local) {

                String obj = "0_" + line;

                Local base = (Local) ((InstanceFieldRef) left).getBase();
                storeField(out, in.stack.get(base), fieldName(left), Collections.singleton(obj));
            } // Copy
            else if (left instanceof Local) {
                Set<String> rhs = abstractValuesOf(in, right, u);
                if (rhs.isEmpty()) {
                    out.stack.remove((Local) left);
                } else {
                    out.stack.put((Local) left, rhs);
                }
            } else if (left instanceof InstanceFieldRef
                    && ((InstanceFieldRef) left).getBase() instanceof Local
                    ) {

                Local base = (Local) ((InstanceFieldRef) left).getBase();
                storeField(out, in.stack.get(base), fieldName(left),
                        abstractValuesOf(in, right, u));
            }
        }

        if (u instanceof Stmt && ((Stmt) u).containsInvokeExpr()) {
            Stmt stmt = (Stmt) u;
            InvokeExpr expr = stmt.getInvokeExpr();
            for (SootMethod target : resolveTargets(stmt)) {
                applyCallEffects(out, in, expr,
                        methodSummaries.getOrDefault(target, new MethodSummary()));
            }
        }

        return out;
    }

    // =====================================================
    // NEW: REDUNDANT LOAD ELIMINATION
    // =====================================================
    private void eliminateRedundantLoad(Body body, AssignStmt oldStmt, Local replacement) {
        AssignStmt newStmt = Jimple.v().newAssignStmt(
                oldStmt.getLeftOp(),
                replacement);

        body.getUnits().swapWith(oldStmt, newStmt);
    }

    private void checkRedundantLoads(Body body,
            Map<Unit, State> IN,
            Map<Unit, State> OUT,
            BriefUnitGraph cfg) {

        String key = body.getMethod().getDeclaringClass().getName() + ":"
                + body.getMethod().getName();

        List<String> results = new ArrayList<>();
        List<Map.Entry<AssignStmt, Local>> rewrites = new ArrayList<>();

        for (Unit u : body.getUnits()) {

            if (!(u instanceof AssignStmt)) {
                continue;
            }

            AssignStmt stmt = (AssignStmt) u;

            if (!(stmt.getRightOp() instanceof InstanceFieldRef)) {
                continue;
            }

            InstanceFieldRef f = (InstanceFieldRef) stmt.getRightOp();

            Local base = (Local) f.getBase();
            String field = f.getField().getName();

            State in = IN.get(u);

            if (!in.stack.containsKey(base)) {
                continue;
            }

            Set<String> loaded = new HashSet<>();

            for (String obj : in.stack.get(base)) {
                if (in.heap.containsKey(obj)
                        && in.heap.get(obj).containsKey(field)) {
                    loaded.addAll(in.heap.get(obj).get(field));
                }
            }

            if (loaded.size() != 1) {
                continue;
            }

            String target = loaded.iterator().next();

            for (Local l : in.stack.keySet()) {

                if (l.equals(stmt.getLeftOp())) {
                    continue;
                }

                if (l.getName().startsWith("$")) {
                    continue;
                }

                Set<String> pts = in.stack.get(l);

                if (pts.size() != 1 || !pts.contains(target)) {
                    continue;
                }

                boolean must = true;

                for (Unit pred : cfg.getPredsOf(u)) {
                    State predOut = OUT.get(pred);

                    if (!predOut.stack.containsKey(l)) {
                        must = false;
                        break;
                    }

                    Set<String> predPts = predOut.stack.get(l);

                    if (predPts.size() != 1 || !predPts.contains(target)) {
                        must = false;
                        break;
                    }
                }

                if (!must) {
                    continue;
                }

                int line = getLine(u);
                results.add(line + ":" + stmt.getRightOp() + " " + l);

                rewrites.add(new AbstractMap.SimpleEntry<>(stmt, l));
                break;
            }
        }

        for (Map.Entry<AssignStmt, Local> r : rewrites) {
            eliminateRedundantLoad(body, r.getKey(), r.getValue());
        }

        if (!results.isEmpty()) {
            redundantLoadResults.put(key, results);
        }
    }

    public void printRedundantLoadResults() {
        if (redundantLoadResults.isEmpty()) {
            return;
        }

        System.out.println("\n========== REDUNDANT LOAD ELIMINATION ==========");

        for (String key : redundantLoadResults.keySet()) {

            List<String> lines = redundantLoadResults.get(key);

            Collections.sort(lines,
                    Comparator.comparingInt(
                            s -> Integer.parseInt(
                                    s.split(":")[0])));

            System.out.println(key);

            for (String s : lines) {
                System.out.println(s);
            }
        }
    }
}
