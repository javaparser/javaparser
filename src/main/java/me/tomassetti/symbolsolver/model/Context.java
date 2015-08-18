package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.usages.MethodUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

import java.util.List;
import java.util.Optional;

/**
 * Context is very similar to scope.
 * In the context we look for solving symbols.
 */
public interface Context {

    public Context getParent();

    /* Type resolution */

    default Optional<TypeUsage> solveGenericType(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver);

    /* Symbols resolution */

    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver);

    default Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }

    /* Methods resolution */

    /**
     * We find the method declaration which is the best match for the given name and list of parameters.
     */
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);

    /**
     * Similar to solveMethod but we return a MethodUsage. A MethodUsage corresponds to a MethodDeclaration plus the
     * resolved type variables.
     */
    public default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        SymbolReference<MethodDeclaration> methodSolved = solveMethod(name, parameterTypes, typeSolver);
        if (methodSolved.isSolved()) {
            MethodDeclaration methodDeclaration = methodSolved.getCorrespondingDeclaration();
            return Optional.of(methodDeclaration.resolveTypeVariables(this, typeSolver));
        } else {
            return Optional.empty();
        }
    }
}
