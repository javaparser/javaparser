package me.tomassetti.symbolsolver.model.declarations;

/**
 * @author Federico Tomassetti
 */
public interface ParameterDeclaration extends ValueDeclaration {

    @Override
    default boolean isField() {
        return false;
    }

    @Override
    default boolean isParameter() {
        return true;
    }

    @Override
    default boolean isVariable() {
        return false;
    }

    @Override
    default boolean isType() {
        return false;
    }

}
