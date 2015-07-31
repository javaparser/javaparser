package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Context is very similar to scope.
 */
public interface Context {
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver);
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver);
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeUsage> parameterTypes, TypeSolver typeSolver);
    public Context getParent();
    public boolean isRoot();
}
