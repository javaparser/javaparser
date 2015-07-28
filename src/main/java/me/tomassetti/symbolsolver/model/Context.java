package me.tomassetti.symbolsolver.model;

import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public interface Context {
    public SymbolReference solveSymbol(String name, TypeSolver typeSolver);
    public MethodReference solveMethod(String name, List<TypeReference> parameterTypes, TypeSolver typeSolver);
    public Context getParent();
    public boolean isRoot();
}
