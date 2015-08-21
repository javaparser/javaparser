package me.tomassetti.symbolsolver.model.declarations;

/**
 * An interface declaration.
 */
public interface InterfaceDeclaration extends TypeDeclaration, TypeParametrized {

    @Override
    default boolean isInterface() {
        return true;
    }

}
