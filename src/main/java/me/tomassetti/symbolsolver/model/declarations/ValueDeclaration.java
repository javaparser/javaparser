package me.tomassetti.symbolsolver.model.declarations;

/**
 * Created by federico on 28/07/15.
 */
public interface ValueDeclaration extends Declaration {

    TypeDeclaration asTypeDeclaration();

    TypeDeclaration getType();
}
