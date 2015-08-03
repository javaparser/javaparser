package me.tomassetti.symbolsolver.model.declarations;

/**
 * A generic declaration.
 */
public interface Declaration {
    String getName();
    boolean isField();
    boolean isParameter();
    boolean isType();
}
