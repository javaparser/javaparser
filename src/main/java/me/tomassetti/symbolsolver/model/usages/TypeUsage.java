package me.tomassetti.symbolsolver.model.usages;

import me.tomassetti.symbolsolver.model.*;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

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

    Optional<TypeUsage> parameterByName(String name);

    boolean isFunctionOrPredicate();

    /**
     * Class, interface and enum are reference-type
     * @return
     */
    boolean isReferenceType();

    String getTypeName();

    default String getTypeNameWithParams() {
        StringBuffer sb = new StringBuffer();
        sb.append(getTypeName());
        if (parameters().size() > 0){
            sb.append("<");
            boolean first = true;
            for (TypeUsage param : parameters()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(param.getTypeNameWithParams());
            }
            sb.append(">");
        }
        return sb.toString();
    }

    TypeUsage getBaseType();

    /* Represent the position of the reference, it is used when solving symbols
     * because a reference to a class A could be related to different classes depending on the position
     * of the reference
     */
    Context getContext();

    SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);
    default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    List<TypeUsage> parameters();

    boolean isTypeVariable();

    default Optional<Value> getField(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeParameter asTypeParameter() {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    /**
     * Create a copy of the value with the type parameter changed.
     * @param i
     * @param replaced
     * @return
     */
    default TypeUsage replaceParam(int i, TypeUsage replaced) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default Optional<TypeUsage> solveGenericType(String name) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    default TypeUsage solveGenericTypes(Context context, TypeSolver typeSolver) {
        if (isTypeVariable()) {
            Optional<TypeUsage> solved = context.solveGenericType(getTypeName(), typeSolver);
            if (solved.isPresent()) {
                return solved.get();
            } else {
                throw new UnsolvedSymbolException(context, getTypeName());
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
}
