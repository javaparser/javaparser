package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

/**
 * Created by federico on 28/07/15.
 */
public interface TypeSolver {

    public SymbolReference<TypeDeclaration> tryToSolveType(String name);

    public default TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name);
        }
    }

}
