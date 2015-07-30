package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Context is very similar to scope.
 */
public interface Context {
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver);
    public SymbolReference<ClassDeclaration> solveType(String name, TypeSolver typeSolver);
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver);
    public Context getParent();
    public boolean isRoot();
}
