package cycle;

import static cycle.CycleA.*;

/**
 * Where resolution starts. "Target" is not a member of CycleA, so the lookup follows CycleA's static
 * imports into the CycleA/CycleB cycle before it can conclude that Target is a type in this package.
 */
public class EntryPoint {

    public String objCode() {
        return Target.OBJCODE;
    }
}
