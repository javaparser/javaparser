package me.tomassetti.symbolsolver.model.declarations;

/**
 * A declaration of a constructor.
 *
 * @author Federico Tomassetti
 */
public interface ConstructorDeclaration extends MethodLikeDeclaration {

    boolean isDefaultMethod();
}
