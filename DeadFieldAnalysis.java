import soot.*;
import soot.jimple.*;
import java.util.*;

public class DeadFieldAnalysis extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        Set<SootField> allFields = new HashSet<>();
        Set<SootField> liveFields = new HashSet<>();

        // Step 1: Collect all fields from application classes
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootField sf : sc.getFields()) {
                allFields.add(sf);
            }
        }

        // Step 3 & 4: Traverse all methods to find field reads
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod sm : sc.getMethods()) {
                if (!sm.isConcrete())
                    continue;

                Body body = sm.retrieveActiveBody();
                for (Unit u : body.getUnits()) {
                    // Check all use boxes for FieldRefs.
                    // In Jimple, reading a field corresponds to the field appearing in a use box
                    // (e.g., right-hand side of an AssignStmt, or used in an expression).
                    for (ValueBox useBox : u.getUseBoxes()) {
                        Value v = useBox.getValue();
                        if (v instanceof FieldRef) {
                            liveFields.add(((FieldRef) v).getField());
                        }
                    }

                    // Note on Step 4:
                    // If a field is written to (e.g. obj.f = 10), it appears in a def box,
                    // not a use box. So we correctly only count field reads here.
                }
            }
        }

        // Step 6: Identify Dead Fields
        List<SootField> deadFields = new ArrayList<>();
        for (SootField sf : allFields) {
            if (!liveFields.contains(sf)) {
                deadFields.add(sf);
            }
        }

        // Keep output deterministic by sorting
        deadFields.sort(Comparator
                .comparing((SootField sf) -> sf.getDeclaringClass().getName())
                .thenComparing(SootField::getName));

        for (SootField sf : deadFields) {
            // Format: [DEAD FIELD] <ClassName>.<fieldName> : <Type>
            System.out.println(
                    "[DEAD FIELD] " + sf.getDeclaringClass().getName() + "." + sf.getName() + " : " + sf.getType());
        }
    }
}
