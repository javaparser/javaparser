package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;

/**
 * A declaration of a method (either in an interface, a class or an enum).
 */
public interface MethodDeclaration extends Declaration, TypeParametrized {

    TypeDeclaration declaringType();

    TypeDeclaration getReturnType();

    int getNoParams();

    ParameterDeclaration getParam(int i);

    /**
     * Get how the method is used in the given context.
     * @param node
     * @return
     */
    MethodUsage getUsage(Node node);
}
