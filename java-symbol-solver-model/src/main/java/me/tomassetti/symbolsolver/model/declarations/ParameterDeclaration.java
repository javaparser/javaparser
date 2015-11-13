package me.tomassetti.symbolsolver.model.declarations;

/**
 * @author Federico Tomassetti
 */
public interface ParameterDeclaration extends ValueDeclaration {

    @Override
    default boolean isParameter() {
        return true;
    }

}
