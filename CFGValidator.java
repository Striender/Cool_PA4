import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.*;

import java.util.*;

public class CFGValidator extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod sm : sc.getMethods()) {
                if (!sm.isConcrete()) continue;

                Body body = sm.retrieveActiveBody();
                validateCFG(sm, body);
            }
        }
    }

    private void validateCFG(SootMethod method, Body body) {
        Map<Unit, Set<Unit>> mySucc = new HashMap<>();
        Map<Unit, Set<Unit>> sootSucc = new HashMap<>();

        // 1. Build Custom CFG
        for (Unit u : body.getUnits()) {
            Set<Unit> succs = new HashSet<>();
            Unit next = body.getUnits().getSuccOf(u);

            if (u instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) u;
                succs.add(ifStmt.getTarget());
                if (next != null) succs.add(next);
            } else if (u instanceof GotoStmt) {
                GotoStmt gotoStmt = (GotoStmt) u;
                succs.add((Unit) gotoStmt.getTarget());
            } else if (u instanceof ReturnStmt || u instanceof ReturnVoidStmt || u instanceof ThrowStmt || u instanceof RetStmt) {
                // No normal successors
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
                // All other statements
                if (next != null) {
                    succs.add(next);
                }
            }
            mySucc.put(u, succs);
        }

        // 2. Build Soot CFG
        // Soot's BriefUnitGraph strictly considers normal control flow edges
        // which completely eliminates the need to filter out exceptional edges
        UnitGraph sootCFG = new BriefUnitGraph(body);
        for (Unit u : body.getUnits()) {
            sootSucc.put(u, new HashSet<>(sootCFG.getSuccsOf(u)));
        }

        // 3. Compare CFGs
        boolean hasMismatch = false;

        for (Unit u : body.getUnits()) {
            Set<Unit> mine = mySucc.get(u);
            Set<Unit> soot = sootSucc.get(u);

            // Compute missing (in soot CFG, but not in custom CFG)
            Set<Unit> missing = new HashSet<>(soot);
            missing.removeAll(mine);

            // Compute extra (in custom CFG, but not in soot CFG)
            Set<Unit> extra = new HashSet<>(mine);
            extra.removeAll(soot);

            if (!missing.isEmpty() || !extra.isEmpty()) {
                hasMismatch = true;
                System.out.println("[CFG MISMATCH] Method: " + method.getDeclaringClass().getName() + "." + method.getName());
                System.out.println("Unit: " + u);
                
                if (!missing.isEmpty()) {
                    System.out.println("Missing successors:");
                    for (Unit m : missing) System.out.println("    " + m);
                }
                if (!extra.isEmpty()) {
                    System.out.println("Extra successors:");
                    for (Unit e : extra) System.out.println("    " + e);
                }

                System.out.println("\n[MY CFG]");
                System.out.println("u \u2192 " + mine);
                System.out.println("\n[SOOT CFG]");
                System.out.println("u \u2192 " + soot + "\n");
            }
        }

        if (!hasMismatch) {
            System.out.println("[CFG CHECK PASSED] " + method.getDeclaringClass().getName() + "." + method.getName());
        }
    }
}
