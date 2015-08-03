package me.tomassetti.symbolsolver.model.typesolvers;

import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

/**
 * Created by federico on 01/08/15.
 */
public class JavaParserTypeSolver implements TypeSolver {

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        throw new UnsupportedOperationException();
    }
}
