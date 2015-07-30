package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.Optional;

/**
 * Created by federico on 28/07/15.
 */
public interface TypeSolver {

    public SymbolReference<ClassDeclaration> tryToSolveType(String name);

    public ClassDeclaration solveType(String name) throws UnsolvedSymbolException;

}
