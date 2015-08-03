package me.tomassetti.symbolsolver.model.typesolvers;

import me.tomassetti.symbolsolver.model.declarations.ClassDeclaration;
import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

/**
 * Created by federico on 30/07/15.
 */
public class DummyTypeSolver implements TypeSolver {

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        return SymbolReference.unsolved(TypeDeclaration.class);
    }

    @Override
    public ClassDeclaration solveType(String name) throws UnsolvedSymbolException {
        throw new UnsolvedSymbolException(null, name);
    }
}
