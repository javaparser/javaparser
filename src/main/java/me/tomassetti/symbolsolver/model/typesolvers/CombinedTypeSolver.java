package me.tomassetti.symbolsolver.model.typesolvers;

import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.UnsolvedSymbolException;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class CombinedTypeSolver implements TypeSolver {

    private List<TypeSolver> elements = new ArrayList<>();

    public void add(TypeSolver typeSolver){
        this.elements.add(typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        for (TypeSolver ts : elements){
            SymbolReference<TypeDeclaration> res = ts.tryToSolveType(name);
            if (res.isSolved()) {
                return res;
            }
        }
        return SymbolReference.unsolved(TypeDeclaration.class);
    }

    @Override
    public TypeDeclaration solveType(String name) throws UnsolvedSymbolException {
        SymbolReference<TypeDeclaration> res = tryToSolveType(name);
        if (res.isSolved()) {
            return res.getCorrespondingDeclaration();
        } else {
            throw new UnsolvedSymbolException(null, name);
        }
    }
}
