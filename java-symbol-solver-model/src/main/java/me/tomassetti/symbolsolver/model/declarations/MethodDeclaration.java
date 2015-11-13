package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;

import java.util.List;

/**
 * A declaration of a method (either in an interface, a class or an enum).
 */
public interface MethodDeclaration extends Declaration, TypeParametrized {

    /**
     * The type in which the method is declared.
     *
     * @return
     */
    TypeDeclaration declaringType();

    TypeUsage getReturnType();

    int getNoParams();

    ParameterDeclaration getParam(int i);

    /**
     * Create the MethodUsage corresponding to this declaration with all generic types solved in the given
     * context.
     */
    @Deprecated
    MethodUsage resolveTypeVariables(Context context, List<TypeUsage> parameterTypes);

    @Deprecated
    Context getContext();

    boolean isAbstract();

    boolean isPrivate();

    boolean isPackageProtected();
}
