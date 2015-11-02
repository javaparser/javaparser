package me.tomassetti.symbolsolver.model.declarations;

/**
 * @author Federico Tomassetti
 */
public interface FieldDeclaration extends ValueDeclaration {

    @Override
    default boolean isField() {
        return true;
    }

    @Override
    default FieldDeclaration asField() {
        return this;
    }

}
