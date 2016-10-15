package me.tomassetti.symbolsolver.model.declarations;

/**
 * Declaration of a parameter.
 *
 * @author Federico Tomassetti
 */
public interface ParameterDeclaration extends ValueDeclaration {

    @Override
    default boolean isParameter() {
        return true;
    }

    boolean isVariadic();

    default String describeType() {
        if (isVariadic()) {
            return getType().asArrayType().getComponentType().describe() + "...";
        } else {
            return getType().describe();
        }
    }
}
