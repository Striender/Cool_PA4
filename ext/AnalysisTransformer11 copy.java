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

        Map<Local, Set<String>> stack;
        Map<String, Map<String, Set<String>>> heap;

        // Available memory locations (obj.field)
        Set<String> available;

        State() {
            stack = new HashMap<>();
            heap = new HashMap<>();
            available = new HashSet<>();
        }

        State(State other) {

            stack = new HashMap<>();
            heap = new HashMap<>();
            available = new HashSet<>(other.available);

            for (Local l : other.stack.keySet()) {
                stack.put(l,
                        new HashSet<>(other.stack.get(l)));
            }

            for (String obj : other.heap.keySet()) {

                Map<String, Set<String>> fieldMap = new HashMap<>();

                for (String field : other.heap.get(obj).keySet()) {

                    fieldMap.put(field,
                            new HashSet<>(
                                    other.heap.get(obj).get(field)));
                }

                heap.put(obj, fieldMap);
            }
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof State))
                return false;
            State s = (State) o;
            return stack.equals(s.stack)
                    && heap.equals(s.heap)
                    && available.equals(s.available);
        }

        @Override
        public int hashCode() {
            return Objects.hash(stack, heap, available);
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

                for (Unit succ : cfg.getSuccsOf(u)) {
                    worklist.add(succ);
                }
            }
        }

    System.out.println("\n=========== FINAL STABLE IN/OUT STATES ===========\n");

    for (Unit u : units) {

    System.out.println("==================================================");
    System.out.println("Statement: " + u);

    printState("IN", u, IN.get(u));
    printState("OUT", u, OUT.get(u));
    }

        checkRedundantLoads(body, IN);
    }

    // =====================================================
    // MERGE
    // =====================================================
    private State merge(Unit u,
            BriefUnitGraph cfg,
            Map<Unit, State> OUT) {

        List<Unit> preds = cfg.getPredsOf(u);

        if (preds.isEmpty())
            return new State();

        State merged = new State(OUT.get(preds.get(0)));

        for (int i = 1; i < preds.size(); i++) {

            State s = OUT.get(preds.get(i));

            // STACK union
            for (Local l : s.stack.keySet()) {
                merged.stack
                        .computeIfAbsent(l, k -> new HashSet<>())
                        .addAll(s.stack.get(l));
            }

            // HEAP union
            for (String obj : s.heap.keySet()) {

                merged.heap
                        .computeIfAbsent(obj, k -> new HashMap<>());

                for (String field : s.heap.get(obj).keySet()) {

                    merged.heap.get(obj)
                            .computeIfAbsent(field,
                                    k -> new HashSet<>())
                            .addAll(s.heap.get(obj).get(field));
                }
            }

            // AVAILABLE intersection
            merged.available.retainAll(s.available);
        }

        return merged;
    }

    // =====================================================
    // TRANSFER
    // =====================================================
    private State transfer(Unit u, State in) {

        State out = new State(in);

        if (u instanceof InvokeStmt) {
            out.available.clear();
            return out;
        }

        if (!(u instanceof AssignStmt))
            return out;

        AssignStmt stmt = (AssignStmt) u;
        Value left = stmt.getLeftOp();
        Value right = stmt.getRightOp();

        // Allocation
        if (right instanceof NewExpr && left instanceof Local) {

            String heapID = "O_" + u.getJavaSourceStartLineNumber();

            Set<String> pts = new HashSet<>();
            pts.add(heapID);
            out.stack.put((Local) left, pts);

            out.heap.putIfAbsent(heapID, new HashMap<>());
        }

        // Copy
        else if (right instanceof Local && left instanceof Local) {

            if (in.stack.containsKey(right)) {
                out.stack.put((Local) left,
                        new HashSet<>(in.stack.get(right)));
            }
        }

        // Store
        else if (left instanceof InstanceFieldRef) {

            InstanceFieldRef fieldRef = (InstanceFieldRef) left;

            Local base = (Local) fieldRef.getBase();
            String field = fieldRef.getField().getName();

            if (!in.stack.containsKey(base))
                return out;

            Set<String> baseObjs = in.stack.get(base);
            Set<String> valueSet = new HashSet<>();

            // Case 1: RHS is local
            if (right instanceof Local
                    && in.stack.containsKey(right)) {

                valueSet.addAll(in.stack.get(right));
            }

            // Case 2: RHS is constant
            else if (right instanceof Constant) {

                String val = "CONST@" + right.toString()
                        + "@L" + u.getJavaSourceStartLineNumber();

                valueSet.add(val);
            }

            // Unknown value fallback
            else {
                String sym = "SYM@L" + u.getJavaSourceStartLineNumber();
                valueSet.add(sym);
            }

            for (String obj : baseObjs) {

                out.heap
                        .computeIfAbsent(obj,
                                k -> new HashMap<>())
                        .put(field,
                                new HashSet<>(valueSet));

                out.available.remove(obj + "." + field);
            }
        }

        // Load
        else if (right instanceof InstanceFieldRef) {

            InstanceFieldRef fieldRef = (InstanceFieldRef) right;

            Local base = (Local) fieldRef.getBase();
            String field = fieldRef.getField().getName();

            if (!in.stack.containsKey(base))
                return out;

            Set<String> result = new HashSet<>();

            for (String obj : in.stack.get(base)) {

                if (in.heap.containsKey(obj)
                        && in.heap.get(obj).containsKey(field)) {

                    result.addAll(
                            in.heap.get(obj).get(field));
                }
            }

            if (left instanceof Local)
                out.stack.put((Local) left, result);

            // Mark location available
            for (String obj : in.stack.get(base)) {
                out.available.add(obj + "." + field);
            }
        }

        return out;
    }

    // =====================================================
    // REDUNDANCY CHECK
    // =====================================================

    private void checkRedundantLoads(Body body,
            Map<Unit, State> IN) {

        String className = body.getMethod().getDeclaringClass().getName();
        String methodName = body.getMethod().getName();

        List<String> results = new ArrayList<>();

        for (Unit u : body.getUnits()) {

            if (!(u instanceof AssignStmt))
                continue;

            AssignStmt stmt = (AssignStmt) u;
            Value right = stmt.getRightOp();

            if (!(right instanceof InstanceFieldRef))
                continue;

            InstanceFieldRef fieldRef = (InstanceFieldRef) right;

            Local base = (Local) fieldRef.getBase();
            String field = fieldRef.getField().getName();

            State in = IN.get(u);

            if (!in.stack.containsKey(base))
                continue;

            // -----------------------------
            // Compute value of this load
            // -----------------------------
            Set<String> loadedObjs = new HashSet<>();

            for (String obj : in.stack.get(base)) {

                if (in.heap.containsKey(obj)
                        && in.heap.get(obj).containsKey(field)) {

                    loadedObjs.addAll(
                            in.heap.get(obj).get(field));
                }
            }

            if (loadedObjs.isEmpty())
                continue;

            // -----------------------------
            // Check if any AVAILABLE load
            // produces same value
            // -----------------------------
            boolean valueAvailable = false;

            for (String loc : in.available) {

                String[] parts = loc.split("\\.");
                String obj = parts[0];
                String fld = parts[1];

                if (in.heap.containsKey(obj)
                        && in.heap.get(obj).containsKey(fld)) {

                    Set<String> val = in.heap.get(obj).get(fld);

                    if (val.equals(loadedObjs)) {
                        valueAvailable = true;
                        break;
                    }
                }
            }

            if (!valueAvailable)
                continue;

            // -----------------------------
            // Find replacement variable
            // -----------------------------
            String replacementVar = null;

            for (Local l : in.stack.keySet()) {

                if (l.equals(stmt.getLeftOp()))
                    continue;

                if (in.stack.get(l).equals(loadedObjs)) {
                    replacementVar = l.toString();
                    break;
                }
            }

            if (replacementVar != null) {

                int line = u.getJavaSourceStartLineNumber();

                results.add(line + ":" +
                        right.toString() + " "
                        + replacementVar);
            }
        }

        if (!results.isEmpty()) {

            String key = className + ":" + methodName;

            finalResults
                    .computeIfAbsent(key, k -> new ArrayList<>())
                    .addAll(results);
        }
    }

    public static void printFinalResults() {

        for (String key : finalResults.keySet()) {

            List<String> lines = finalResults.get(key);

            if (lines == null || lines.isEmpty())
                continue;

            // Sort by numeric line number
            Collections.sort(lines, (a, b) -> {

                int lineA = Integer.parseInt(a.split(":")[0]);
                int lineB = Integer.parseInt(b.split(":")[0]);

                return Integer.compare(lineA, lineB);
            });

            System.out.println(key);

            for (String s : lines) {
                System.out.println(s);
            }
        }
    }


    //this is to print the in and OUT 
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

        System.out.println("  AVAILABLE:");
        for (String a : s.available) {
            System.out.println("    " + a);
        }

        System.out.println("--------------------------------------------------");
    }

}
