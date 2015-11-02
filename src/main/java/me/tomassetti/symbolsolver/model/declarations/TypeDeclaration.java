package me.tomassetti.symbolsolver.model.declarations;

import me.tomassetti.symbolsolver.model.invokations.MethodUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.Context;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import java.util.List;
import java.util.Optional;

/**
 * A declaration of a type. It could be a primitive type, an enum, a class, an interface or a type variable.
 * It cannot be an annotation or an array.
 *
 * @author Federico Tomassetti
 */
public interface TypeDeclaration extends Declaration, TypeParametrized {
    String getQualifiedName();

    @Deprecated
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes);

    @Deprecated
    default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext, List<TypeUsage> typeParameterValues) {
        return getContext().solveMethodAsUsage(name, parameterTypes, typeSolver);
    }

    boolean isAssignableBy(TypeUsage typeUsage);

    default boolean canBeAssignedTo(TypeDeclaration other) {
        return other.isAssignableBy(this);
    }

    FieldDeclaration getField(String name);

    boolean hasField(String name);

    boolean isAssignableBy(TypeDeclaration other);


    SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver);

    /**
     * Try to solve a symbol just in the declaration, it does not delegate to the container.
     *
     * @param substring
     * @param typeSolver
     * @return
     */
    SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver);

    List<ReferenceTypeUsage> getAllAncestors();

    default boolean isClass() {
        return false;
    }

    default boolean isInterface() {
        return false;
    }

    default boolean isEnum() {
        return false;
    }

    default boolean isTypeVariable() {
        return false;
    }

    @Override
    default boolean isType() {
        return true;
    }

    @Override
    default TypeDeclaration asType() {
        return this;
    }

    default ClassDeclaration asClass() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default InterfaceDeclaration asInterface() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
