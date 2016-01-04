package me.tomassetti.symbolsolver.model.resolution;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * @author Federico Tomassetti
 */
public interface TypeSolver {

    default TypeSolver getRoot() {
        if (getParent() == null) {
            return this;
        } else {
            return getParent().getRoot();
        }
    }

    TypeSolver getParent();

    void setParent(TypeSolver parent);

    SymbolReference<TypeDeclaration> tryToSolveType(String name);

    default TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name, this);
        }
    }

}
