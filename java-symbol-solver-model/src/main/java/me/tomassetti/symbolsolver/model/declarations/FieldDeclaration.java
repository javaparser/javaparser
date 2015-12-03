package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

/**
 * Declaration of a field.
 *
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

    @Deprecated
    default FieldDeclaration replaceType(TypeUsage fieldType) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
