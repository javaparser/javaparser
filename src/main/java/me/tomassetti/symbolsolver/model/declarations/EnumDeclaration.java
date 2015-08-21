package me.tomassetti.symbolsolver.model.declarations;

/**
 * @author Federico Tomassetti
 */
public interface EnumDeclaration extends TypeDeclaration {

    @Override
    default boolean isEnum() {
        return true;
    }
}
