package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.TypeUsage;

/**
 * Created by federico on 28/07/15.
 */
public interface ValueDeclaration extends Declaration {

    TypeDeclaration asTypeDeclaration();

    TypeDeclaration getType();

    default TypeUsage getTypeUsage() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
