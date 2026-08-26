package cycle;

import static cycle.SolvableConstants.*;
import static cycle.CycleB.*;

/**
 * One half of the import cycle: CycleA imports CycleB, CycleB imports CycleA.
 * The order matters -- SolvableConstants is tried first and resolves nothing, so a guard that
 * clears its history on an unsolved lookup is already empty by the time CycleB is reached.
 */
public final class CycleA {}
