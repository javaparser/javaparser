package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;

/**
 * A declaration of a method (either in an interface, a class or an enum).
 */
public interface MethodDeclaration extends Declaration, TypeParametrized {

    /**
     * The type in which the method is declared.
     * @return
     */
    TypeDeclaration declaringType();

    TypeUsage getReturnType(TypeSolver typeSolver);

    int getNoParams();

    ParameterDeclaration getParam(int i);

    /**
     * Create the MethodUsage corresponding to this declaration with all generic types solved in the given
     * context.
     */
    MethodUsage resolveTypeVariables(Context context, TypeSolver typeSolver, List<TypeUsage> parameterTypes);

    Context getContext();
}
