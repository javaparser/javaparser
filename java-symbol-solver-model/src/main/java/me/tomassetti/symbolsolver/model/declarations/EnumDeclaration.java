package me.tomassetti.symbolsolver.model.declarations;

/**
 * Declaration of an Enum.
 *
 * @author Federico Tomassetti
 */
public interface EnumDeclaration extends TypeDeclaration, HasAccessLevel {

    @Override
    default boolean isEnum() {
        return true;
    }

    @Override
    default EnumDeclaration asEnum() {
        return this;
    }
}
