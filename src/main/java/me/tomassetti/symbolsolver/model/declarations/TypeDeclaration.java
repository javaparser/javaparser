package me.tomassetti.symbolsolver.model.declarations;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.Context;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

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
    Context getContext();

    default SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        return getContext().solveMethod(name, parameterTypes, typeSolver);
    }

    /**
     * Get how the type is used in the given context.
     * @param node
     * @return
     */
    TypeUsage getUsage(Node node);

    boolean isAssignableBy(TypeUsage typeUsage, TypeSolver typeSolver);

    default boolean canBeAssignedTo(TypeDeclaration other, TypeSolver typeSolver) {
        return other.isAssignableBy(this, typeSolver);
    }

    FieldDeclaration getField(String name, TypeSolver typeSolver);

    boolean hasField(String name, TypeSolver typeSolver);

    default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver, Context invokationContext) {
        return getContext().solveMethodAsUsage(name, parameterTypes, typeSolver);
    }

    default boolean isAssignableBy(TypeDeclaration other, TypeSolver typeSolver) {
        return isAssignableBy(new TypeUsageOfTypeDeclaration(other), typeSolver);
    }

    SymbolReference<? extends ValueDeclaration> solveSymbol(String substring, TypeSolver typeSolver);

    /**
     * Try to solve a symbol just in the declaration, it does not delegate to the container.
     * @param substring
     * @param typeSolver
     * @return
     */
    SymbolReference<TypeDeclaration> solveType(String substring, TypeSolver typeSolver);

    List<TypeDeclaration> getAllAncestors(TypeSolver typeSolver);

    default boolean isClass() {
        return false;
    }

    default boolean isInterface() {
        return false;
    }

    default boolean isEnum() {
        return false;
    }

    default boolean isTypeVariable() { return false; }

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
