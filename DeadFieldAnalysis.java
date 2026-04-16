import soot.*;
import soot.jimple.*;
import java.util.*;

public class DeadFieldAnalysis extends SceneTransformer {

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        Set<SootField> liveFields = new HashSet<>();
        Set<SootField> allFieldRefs = new HashSet<>();

        // Traversal 1: Find all field reads (liveFields) and all field references (allFieldRefs)
        for (SootClass sc : Scene.v().getApplicationClasses()) {
            for (SootMethod sm : sc.getMethods()) {
                if (!sm.isConcrete()) continue;
                
                Body body = sm.retrieveActiveBody();
                for (Unit u : body.getUnits()) {
                    // Check use boxes (Reads)
                    for (ValueBox useBox : u.getUseBoxes()) {
                        Value v = useBox.getValue();
                        if (v instanceof FieldRef) {
                            SootField f = ((FieldRef) v).getField();
                            liveFields.add(f);
                            allFieldRefs.add(f);
                        }
                    }
                    
                    // Check def boxes (Writes)
                    for (ValueBox defBox : u.getDefBoxes()) {
                        Value v = defBox.getValue();
                        if (v instanceof FieldRef) {
                            SootField f = ((FieldRef) v).getField();
                            allFieldRefs.add(f);
                        }
                    }
                }
            }
        }

        // Traversal 2: Filter and removing dead fields cleanly
        // Using List for deterministic output iteration first, then remove from actual class
        List<SootField> removedFields = new ArrayList<>();

        for (SootClass sc : Scene.v().getApplicationClasses()) {
            // Need the iterator to safely remove from the chain
            Iterator<SootField> it = sc.getFields().iterator();
            while (it.hasNext()) {
                SootField f = it.next();
                
                // Is the field never read?
                if (!liveFields.contains(f)) {
                    // Safety check: is it referenced anywhere else?
                    if (!allFieldRefs.contains(f)) {
                        it.remove();
                        removedFields.add(f);
                    }
                }
            }
        }

        // Keep output deterministic by sorting class -> field
        removedFields.sort(Comparator
            .comparing((SootField sf) -> sf.getDeclaringClass().getName())
            .thenComparing(SootField::getName));

        for (SootField f : removedFields) {
            System.out.println("[REMOVED DEAD FIELD] " + f.getDeclaringClass().getName() + "." + f.getName());
        }
    }
}
