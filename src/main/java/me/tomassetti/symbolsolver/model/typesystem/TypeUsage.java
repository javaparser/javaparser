package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * A usage of a type. It could be a primitive type or a reference type (enum, class, interface).
 * In the later case it could take type parameters (other TypeUsages). It could also be a TypeVariable, like in:
 *
 * class A<B> { }
 *
 * where B is a TypeVariable. It could also be Wildcard Type, possibly with constraints.
 */
public interface TypeUsage {

    ///
    /// Relation with other types
    ///

    /**
     * Does this type represent an array?
     */
    default boolean isArray() {
        return false;
    }

    /**
     * Is this a primitive type?
     */
    default boolean isPrimitive() {
        return false;
    }

    /**
     * Is this the null type?
     */
    default boolean isNull() {
        return false;
    }

    /**
     * Is this a non primitive value?
     */
    default boolean isReference() {
        return isReferenceType() || isArray() || isTypeVariable() || isNull();
    }

    /**
     * Can this be seen as a ReferenceTypeUsage?
     * In other words: is this a reference to a class, an interface or an enum?
     */
    default boolean isReferenceType() {
        return false;
    }

    default boolean isVoid() {
        return false;
    }

    default boolean isTypeVariable() {
        return false;
    }

    ///
    /// Downcasting
    ///

    default ReferenceTypeUsage asReferenceTypeUsage() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeParameter asTypeParameter() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    ///
    /// Naming
    ///

    String describe();

    // There should be just describe
    @Deprecated
    default String describeWithParams() {
        StringBuffer sb = new StringBuffer();
        sb.append(describe());
        if (parameters().size() > 0){
            sb.append("<");
            boolean first = true;
            for (TypeUsage param : parameters()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(param.describeWithParams());
            }
            sb.append(">");
        }
        return sb.toString();
    }

    String getQualifiedName();

    String prettyPrint();

    ///
    /// TypeParameters
    ///

    /**
     * Create a copy of the value with the type parameter changed.
     * @param i
     * @param replaced
     * @return
     */
    default TypeUsage replaceParam(int i, TypeUsage replaced) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeUsage replaceParam(String name, TypeUsage replaced) {
        //throw new UnsupportedOperationException(this.getClass().getCanonicalName());
        return this;
    }

    default Optional<TypeUsage> solveGenericType(String name) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeUsage solveGenericTypes(Context context, TypeSolver typeSolver) {
        if (isTypeVariable()) {
            Optional<TypeUsage> solved = context.solveGenericType(describe(), typeSolver);
            if (solved.isPresent()) {
                return solved.get();
            } else {
                throw new UnsolvedSymbolException(context, describe());
            }
        } else {
            TypeUsage result = this;
            int i=0;
            for (TypeUsage tp : this.parameters()) {
                result = result.replaceParam(i, tp.solveGenericTypes(context, typeSolver));
                i++;
            }
            return result;
        }
    }

    List<TypeUsage> parameters();

    ///
    /// Methods
    ///

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);
    default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    ///
    /// Fields
    ///

    default Optional<Value> getField(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    ///
    /// Relation with other types
    ///

    boolean isAssignableBy(TypeUsage other, TypeSolver typeSolver);

    // Move to ReferenceTypeUsage
    @Deprecated
    default List<ReferenceTypeUsage> getAllAncestors(TypeSolver typeSolver) {
        return Collections.emptyList();
    }
}
