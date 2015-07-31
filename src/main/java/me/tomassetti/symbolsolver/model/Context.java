package me.tomassetti.symbolsolver.model;

import com.github.javaparser.ast.type.Type;

import java.util.List;

/**
 * Context is very similar to scope.
 */
public interface Context {
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver);
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver);
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver);
    public Context getParent();
    public boolean isRoot();
}
