package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;

/**
 * A declaration of a method (either in an interface, a class or an enum).
 */
public interface MethodDeclaration extends Declaration, TypeParametrized {

    /**
     * The type in which the method is declared.
     * @return
     */
    TypeDeclaration declaringType();

    TypeDeclaration getReturnType(TypeSolver typeSolver);

    int getNoParams();

    ParameterDeclaration getParam(int i);

    /**
     * Get how the method is used in the given context.
     * @param node
     * @return
     */
    MethodUsage getUsage(Node node);

    /**
     * Create the MethodUsage corresponding to this declaration with all generic types solved in the given
     * context.
     */
    MethodUsage resolveTypeVariables(Context context, TypeSolver typeSolver);

    Context getContext();
}
