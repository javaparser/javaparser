package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.resolution.Context;

import java.util.List;

/**
 * A declaration of a method (either in an interface, a class, an enum or an annotation).
 *
 * @author Federico Tomassetti
 */
public interface MethodDeclaration extends Declaration, TypeParametrized {

    /**
     * The type in which the method is declared.
     */
    TypeDeclaration declaringType();

    TypeUsage getReturnType();

    int getNoParams();

    ParameterDeclaration getParam(int i);

    default ParameterDeclaration getLastParam() {
        if (getNoParams() == 0) {
            throw new UnsupportedOperationException();
        }
        return getParam(getNoParams() - 1);
    }

    /**
     * Note that when a method has a variadic parameter it should have an array type.
     * @return
     */
    default boolean hasVariadicParameter() {
        if (getNoParams() == 0) {
            return false;
        } else {
            return getParam(getNoParams() - 1).isVariadic();
        }
    }

    /**
     * Create the MethodUsage corresponding to this declaration with all generic types solved in the given
     * context.
     */
    @Deprecated
    MethodUsage resolveTypeVariables(Context context, List<TypeUsage> parameterTypes);

    boolean isAbstract();

    boolean isPrivate();

    boolean isPackageProtected();
}
