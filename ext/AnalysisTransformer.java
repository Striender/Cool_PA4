import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.Chain;

import java.util.*;

public class AnalysisTransformer extends BodyTransformer {

    public static Map<String, List<String>> finalResults = new TreeMap<>();

    // =====================================================
    // STATE
    // =====================================================
    static class State {

        Map<Local, Set<String>> stack = new HashMap<>();
        Map<String, Map<String, Set<String>>> heap = new HashMap<>();

        State() {
        }

        State(State other) {

            for (Local l : other.stack.keySet())
                stack.put(l, new HashSet<>(other.stack.get(l)));

            for (String obj : other.heap.keySet()) {

                Map<String, Set<String>> fieldMap = new HashMap<>();

                for (String f : other.heap.get(obj).keySet())
                    fieldMap.put(f,
                            new HashSet<>(other.heap.get(obj).get(f)));

                heap.put(obj, fieldMap);
            }
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof State))
                return false;
            State s = (State) o;
            return stack.equals(s.stack) && heap.equals(s.heap);
        }

        @Override
        public int hashCode() {
            return Objects.hash(stack, heap);
        }
    }

    // =====================================================
    // WORKLIST
    // =====================================================
    @Override
    protected void internalTransform(Body body,
            String phaseName,
            Map<String, String> options) {

        if (body.getMethod().isConstructor())
            return;

        BriefUnitGraph cfg = new BriefUnitGraph(body);
        Chain<Unit> units = body.getUnits();

        Map<Unit, State> IN = new HashMap<>();
        Map<Unit, State> OUT = new HashMap<>();

        for (Unit u : units) {
            IN.put(u, new State());
            OUT.put(u, new State());
        }

        Queue<Unit> worklist = new LinkedList<>(units);

        while (!worklist.isEmpty()) {

            Unit u = worklist.poll();

            State newIn = merge(u, cfg, OUT);
            IN.put(u, newIn);

            State oldOut = OUT.get(u);
            State newOut = transfer(u, newIn);

            if (!newOut.equals(oldOut)) {

                OUT.put(u, newOut);

                for (Unit succ : cfg.getSuccsOf(u))
                    worklist.add(succ);
            }
        }

        //System.out.println("\n=========== FINAL STABLE IN/OUT STATES ===========\n");
        //for (Unit u : units) {
        //    System.out.println("==================================================");
        //    System.out.println("Statement: " + u);
        //    printState("IN", u, IN.get(u));
        //    printState("OUT", u, OUT.get(u));
        //}
//
        checkRedundantLoads(body, IN);
    }

    private Set<String> computeReachable(State in, Set<String> seeds) {

        Set<String> visited = new HashSet<>();
        Queue<String> work = new LinkedList<>(seeds);

        while (!work.isEmpty()) {

            String obj = work.poll();

            if (!visited.add(obj))
                continue;

            if (!in.heap.containsKey(obj))
                continue;

            for (Set<String> targets : in.heap.get(obj).values()) {
                for (String t : targets) {
                    if (!visited.contains(t))
                        work.add(t);
                }
            }
        }

        return visited;
    }

    private void injectTop(State out, Unit u) {

        String topObj = "TOP_" +
                u.getJavaSourceStartLineNumber();

        out.heap.put(topObj, new HashMap<>());

        for (Local l : out.stack.keySet()) {

            out.stack.get(l).add(topObj);
        }
    }

    // =====================================================
    // MERGE (UNION)
    // ====================================================

    private State merge(Unit u,
            BriefUnitGraph cfg,
            Map<Unit, State> OUT) {

        List<Unit> preds = cfg.getPredsOf(u);

        if (preds.isEmpty())
            return new State();

        State merged = new State(OUT.get(preds.get(0)));

        for (int i = 1; i < preds.size(); i++) {

            State s = OUT.get(preds.get(i));

            // stack union
            for (Local l : s.stack.keySet())
                merged.stack
                        .computeIfAbsent(l, k -> new HashSet<>())
                        .addAll(s.stack.get(l));

            // heap union
            for (String obj : s.heap.keySet()) {

                merged.heap
                        .computeIfAbsent(obj, k -> new HashMap<>());

                for (String f : s.heap.get(obj).keySet())
                    merged.heap.get(obj)
                            .computeIfAbsent(f, k -> new HashSet<>())
                            .addAll(s.heap.get(obj).get(f));
            }
        }

        return merged;
    }

    // =====================================================
    // TRANSFER
    // =====================================================
    private State transfer(Unit u, State in) {

        State out = new State(in);

        // -------------------------------------------------
        // CALL → add TOP object
        if (u instanceof InvokeStmt ||
                (u instanceof AssignStmt &&
                        ((AssignStmt) u).containsInvokeExpr())) {

            InvokeExpr expr;

            if (u instanceof InvokeStmt)
                expr = ((InvokeStmt) u).getInvokeExpr();
            else
                expr = ((AssignStmt) u).getInvokeExpr();

            // ignore constructor
            if (expr instanceof SpecialInvokeExpr)
                return out;

            Set<String> seeds = new HashSet<>();

            // receiver (for instance calls)
            if (expr instanceof InstanceInvokeExpr) {

                Local base = (Local) ((InstanceInvokeExpr) expr).getBase();

                if (in.stack.containsKey(base))
                    seeds.addAll(in.stack.get(base));
            }

            // arguments
            for (Value arg : expr.getArgs()) {

                if (arg instanceof Local &&
                        in.stack.containsKey(arg)) {

                    seeds.addAll(in.stack.get(arg));
                }
            }

            // compute reachable closure
            Set<String> reachable = computeReachable(in, seeds);

            // create TOP object
            String topObj = "TOP_" + u.getJavaSourceStartLineNumber();

            out.heap.put(topObj, new HashMap<>());

            // poison only reachable objects
            for (String obj : reachable) {

                // add TOP to fields
                if (out.heap.containsKey(obj)) {
                    for (String f : out.heap.get(obj).keySet()) {
                        out.heap.get(obj)
                                .get(f)
                                .add(topObj);
                    }
                }
            }

            // poison only locals pointing to reachable
            for (Local l : out.stack.keySet()) {

                Set<String> pts = out.stack.get(l);

                for (String r : reachable) {
                    if (pts.contains(r)) {
                        pts.add(topObj);
                        break;
                    }
                }
            }

            return out;
        }

        if (u instanceof AssignStmt &&
                ((AssignStmt) u).containsInvokeExpr()) {

            InvokeExpr expr = ((AssignStmt) u).getInvokeExpr();

            if (expr instanceof SpecialInvokeExpr) {
                return out;
            }

            injectTop(out, u);
            return out;
        }

        if (!(u instanceof AssignStmt))
            return out;

        AssignStmt stmt = (AssignStmt) u;
        Value left = stmt.getLeftOp();
        Value right = stmt.getRightOp();

        // Allocation
        if (right instanceof NewExpr &&
                left instanceof Local) {

            String obj = "O_" +
                    u.getJavaSourceStartLineNumber();

            out.stack.put((Local) left,
                    new HashSet<>(Arrays.asList(obj)));

            out.heap.putIfAbsent(obj, new HashMap<>());
        }

        // Copy
        else if (right instanceof Local &&
                left instanceof Local) {

            if (in.stack.containsKey(right))
                out.stack.put((Local) left,
                        new HashSet<>(in.stack.get(right)));
        }

        // Store
        else if (left instanceof InstanceFieldRef) {

            InstanceFieldRef f = (InstanceFieldRef) left;

            Local base = (Local) f.getBase();
            String field = f.getField().getName();

            if (!in.stack.containsKey(base))
                return out;

            Set<String> value = new HashSet<>();

            if (right instanceof Local &&
                    in.stack.containsKey(right)) {

                value.addAll(in.stack.get(right));

            } else if (right instanceof Constant) {

                value.add("CONST_" + right.toString());
            }

            for (String obj : in.stack.get(base)) {

                out.heap
                        .computeIfAbsent(obj,
                                k -> new HashMap<>())
                        .put(field, value);
            }
        }

        // Load
        else if (right instanceof InstanceFieldRef &&
                left instanceof Local) {

            InstanceFieldRef f = (InstanceFieldRef) right;

            Local base = (Local) f.getBase();
            String field = f.getField().getName();

            if (!in.stack.containsKey(base))
                return out;

            Set<String> result = new HashSet<>();

            for (String obj : in.stack.get(base)) {

                if (in.heap.containsKey(obj) &&
                        in.heap.get(obj)
                                .containsKey(field)) {

                    result.addAll(
                            in.heap.get(obj)
                                    .get(field));
                }
            }

            out.stack.put((Local) left, result);
        }

        return out;
    }

    // =====================================================
    // REDUNDANCY CHECK (VALUE BASED)
    // =====================================================
    private void checkRedundantLoads(Body body,
            Map<Unit, State> IN) {

        String key = body.getMethod()
                .getDeclaringClass()
                .getName()
                + ":" +
                body.getMethod().getName();

        List<String> results = new ArrayList<>();

        for (Unit u : body.getUnits()) {

            if (!(u instanceof AssignStmt))
                continue;

            AssignStmt stmt = (AssignStmt) u;

            if (!(stmt.getRightOp() instanceof InstanceFieldRef))
                continue;

            InstanceFieldRef f = (InstanceFieldRef) stmt.getRightOp();

            Local base = (Local) f.getBase();
            String field = f.getField().getName();

            State in = IN.get(u);

            if (!in.stack.containsKey(base))
                continue;

            Set<String> loaded = new HashSet<>();

            for (String obj : in.stack.get(base)) {

                if (in.heap.containsKey(obj) &&
                        in.heap.get(obj)
                                .containsKey(field)) {

                    loaded.addAll(
                            in.heap.get(obj)
                                    .get(field));
                }
            }

            if (loaded.size() != 1)
                continue;

            String target = loaded.iterator().next();

            for (Local l : in.stack.keySet()) {

                if (l.equals(stmt.getLeftOp()))
                    continue;

                if (l.getName().startsWith("$"))
                    continue;

                Set<String> pts = in.stack.get(l);

                if (pts.size() == 1 && pts.contains(target)) {

                    int line = u.getJavaSourceStartLineNumber();

                    results.add(line + ":" +
                            stmt.getRightOp() + " " + l);

                    break;
                }
            }

        }

        if (!results.isEmpty())
            finalResults.put(key, results);
    }

    public static void printFinalResults() {

        for (String key : finalResults.keySet()) {

            List<String> lines = finalResults.get(key);

            Collections.sort(lines,
                    Comparator.comparingInt(
                            s -> Integer.parseInt(
                                    s.split(":")[0])));

            System.out.println(key);

            for (String s : lines)
                System.out.println(s);
        }
    }

    // this is to print the in and OUT
    private void printState(String label, Unit u, State s) {

        System.out.println(label + " of: " + u);

        System.out.println("  STACK:");
        for (Local l : s.stack.keySet()) {
            System.out.println("    " + l + " -> " + s.stack.get(l));
        }

        System.out.println("  HEAP:");
        for (String obj : s.heap.keySet()) {
            System.out.println("    " + obj + ":");
            for (String field : s.heap.get(obj).keySet()) {
                System.out.println("      " + field + " -> "
                        + s.heap.get(obj).get(field));
            }
        }

        System.out.println("--------------------------------------------------");
    }

}
