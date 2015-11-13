package me.tomassetti.symbolsolver.model.resolution;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

public interface TypeSolver {

    public default TypeSolver getRoot() {
        if (getParent() == null) {
            return this;
        } else {
            return getParent().getRoot();
        }
    }

    public TypeSolver getParent();

    void setParent(TypeSolver parent);

    public SymbolReference<TypeDeclaration> tryToSolveType(String name);

    public default TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> ref = tryToSolveType(name);
        if (ref.isSolved()) {
            return ref.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(name, this);
        }
    }

}
