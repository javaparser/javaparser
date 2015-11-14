package me.tomassetti.symbolsolver.model.declarations;

/**
 * Declaration of an Enum.
 *
 * @author Federico Tomassetti
 */
public interface EnumDeclaration extends TypeDeclaration {

    @Override
    default boolean isEnum() {
        return true;
    }
}
