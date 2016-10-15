package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.usages.typesystem.Type;

/**
 * A declaration of a method (either in an interface, a class, an enum or an annotation).
 *
 * @author Federico Tomassetti
 */
public interface MethodDeclaration extends MethodLikeDeclaration {

    Type getReturnType();

    boolean isAbstract();

    boolean isDefaultMethod();
}
