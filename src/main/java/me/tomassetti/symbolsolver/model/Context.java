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
 */
public interface Context {
    default Optional<TypeUsage> solveGenericType(String name) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
    public SymbolReference<ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver);
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver);
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);
    public default Optional<MethodUsage> solveMethodAsUsage(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
    public Context getParent();
    public boolean isRoot();
    default Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {
        throw new UnsupportedOperationException(this.getClass().getCanonicalName());
    }
}
