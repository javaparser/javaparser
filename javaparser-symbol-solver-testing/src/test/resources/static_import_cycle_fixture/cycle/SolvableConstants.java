package cycle;

/**
 * First static import of {@link CycleA}. Resolving a name here fails without recursing, which is what
 * made the old guard flush its search history mid-lookup and let the cycle below escape.
 */
public interface SolvableConstants {
    String ID = "ID";
}
