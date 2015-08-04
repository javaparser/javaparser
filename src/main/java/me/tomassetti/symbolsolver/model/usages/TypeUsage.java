package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;

import java.util.List;
import java.util.Optional;

/**
 * Reference to a type. A TypeRef could be a primitive type or a reference type (enum, class, interface).
 * In the later case it could take type parameters (other TypeRefs). It could also be a TypeVariable, like in:
 *
 * class A<B> { }
 *
 * where B is a TypeVariable. It could also be Wildcard Type, possibly with constraints.
 */
public interface TypeUsage {

    boolean isArray();
    boolean isPrimitive();

    boolean isFunctionOrPredicate();

    /**
     * Class, interface and enum are reference-type
     * @return
     */
    boolean isReferenceType();

    String getTypeName();

    TypeUsage getBaseType();

    /* Represent the position of the reference, it is used when solving symbols
     * because a reference to a class A could be related to different classes depending on the position
     * of the reference
     */
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);

    List<TypeUsage> parameters();

    boolean isTypeVariable();

    default Optional<Value> getField(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeParameter asTypeParameter() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
