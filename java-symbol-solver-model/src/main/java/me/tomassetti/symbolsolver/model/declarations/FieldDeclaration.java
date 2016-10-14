package me.tomassetti.symbolsolver.model.declarations;

/**
 * Declaration of a field.
 *
 * @author Federico Tomassetti
 */
public interface FieldDeclaration extends ValueDeclaration, HasAccessLevel {

    @Override
    default boolean isField() {
        return true;
    }

    @Override
    default FieldDeclaration asField() {
        return this;
    }

}
