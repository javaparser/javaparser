package me.tomassetti.symbolsolver.model.declarations;

/**
 * A generic declaration.
 */
public interface Declaration {
    String getName();
    default boolean isField() {
        return false;
    }
    default boolean isParameter() {
        return false;
    }
    default boolean isVariable() {
        return false;
    }
    default boolean isType() {
        return false;
    }
}
