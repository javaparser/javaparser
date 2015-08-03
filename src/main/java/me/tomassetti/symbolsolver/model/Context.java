package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

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
