import soot.*;
import soot.jimple.*;

import java.util.*;

public class DeadCodeAnalysis extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod sm : sc.getMethods()) {
                if (!sm.isConcrete()) continue;

                Body body = sm.retrieveActiveBody();
                analyzeDeadCode(sm, body);
            }
        }
    }

    private void analyzeDeadCode(SootMethod method, Body body) {
        // 1. Build Custom CFG
        Map<Unit, Set<Unit>> succ = new HashMap<>();
        Map<Unit, Set<Unit>> pred = new HashMap<>();
        
        for (Unit u : body.getUnits()) {
            succ.put(u, new HashSet<>());
            pred.put(u, new HashSet<>());
        }

        for (Unit u : body.getUnits()) {
            Set<Unit> succs = succ.get(u);
            Unit next = body.getUnits().getSuccOf(u);

            if (u instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) u;
                succs.add(ifStmt.getTarget());
                if (next != null) succs.add(next);
            } else if (u instanceof GotoStmt) {
                GotoStmt gotoStmt = (GotoStmt) u;
                succs.add((Unit) gotoStmt.getTarget());
            } else if (u instanceof ReturnStmt || u instanceof ReturnVoidStmt || u instanceof ThrowStmt || u instanceof RetStmt) {
                // No successors
            } else if (u instanceof TableSwitchStmt) {
                TableSwitchStmt sw = (TableSwitchStmt) u;
                for (Unit target : sw.getTargets()) {
                    succs.add(target);
                }
                succs.add((Unit) sw.getDefaultTarget());
            } else if (u instanceof LookupSwitchStmt) {
                LookupSwitchStmt sw = (LookupSwitchStmt) u;
                for (Unit target : sw.getTargets()) {
                    succs.add(target);
                }
                succs.add((Unit) sw.getDefaultTarget());
            } else {
                if (next != null) {
                    succs.add(next);
                }
            }
            
            // Populate pred mapping
            for (Unit s : succs) {
                // Just for safety if branching to a weird block structure
                pred.computeIfAbsent(s, k -> new HashSet<>()).add(u);
            }
        }

        // 2. Compute USE and DEF sets
        Map<Unit, Set<Local>> USE = new HashMap<>();
        Map<Unit, Set<Local>> DEF = new HashMap<>();

        for (Unit u : body.getUnits()) {
            Set<Local> useSet = new HashSet<>();
            for (ValueBox vb : u.getUseBoxes()) {
                if (vb.getValue() instanceof Local) {
                    useSet.add((Local) vb.getValue());
                }
            }
            USE.put(u, useSet);

            Set<Local> defSet = new HashSet<>();
            for (ValueBox vb : u.getDefBoxes()) {
                if (vb.getValue() instanceof Local) {
                    defSet.add((Local) vb.getValue());
                }
            }
            DEF.put(u, defSet);
        }

        // 3. Initialize IN and OUT
        Map<Unit, Set<Local>> IN = new HashMap<>();
        Map<Unit, Set<Local>> OUT = new HashMap<>();
        for (Unit u : body.getUnits()) {
            IN.put(u, new HashSet<>());
            OUT.put(u, new HashSet<>());
        }

        List<Unit> revUnits = new ArrayList<>();
        for (Unit u : body.getUnits()) {
            revUnits.add(u);
        }
        Collections.reverse(revUnits);

        // 4. Fixed-point iteration
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Unit u : revUnits) {
                Set<Local> newOut = new HashSet<>();
                for (Unit s : succ.get(u)) {
                    newOut.addAll(IN.get(s));
                }

                Set<Local> newIn = new HashSet<>(newOut);
                newIn.removeAll(DEF.get(u));
                newIn.addAll(USE.get(u));

                if (!newOut.equals(OUT.get(u)) || !newIn.equals(IN.get(u))) {
                    OUT.put(u, newOut);
                    IN.put(u, newIn);
                    changed = true;
                }
            }
        }

        // 5 & 6. Identify dead statements
        for (Unit u : body.getUnits()) {
            boolean hasDef = !DEF.get(u).isEmpty();
            boolean isDead = false;

            if (hasDef && u instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) u;
                Value left = assign.getLeftOp();

                // Side effect filtering: only LHS=Local and NO invoke
                if (left instanceof Local && !assign.containsInvokeExpr()) {
                    boolean intersection = false;
                    for (Local d : DEF.get(u)) {
                        if (OUT.get(u).contains(d)) {
                            intersection = true;
                            break;
                        }
                    }
                    if (!intersection) {
                        isDead = true;
                    }
                }
            }

            // 7. Output
            if (isDead) {
                System.out.println("[DEAD CODE] " + method.getDeclaringClass().getName() + "." + method.getName() + " : " + u);
            }
        }
    }
}
