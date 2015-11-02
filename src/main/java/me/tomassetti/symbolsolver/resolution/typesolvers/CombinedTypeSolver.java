package me.tomassetti.symbolsolver.resolution.typesolvers;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.resolution.SymbolReference;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.UnsolvedSymbolException;

import java.util.ArrayList;
import java.util.List;

public class CombinedTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private List<TypeSolver> elements = new ArrayList<>();

    public CombinedTypeSolver(TypeSolver... elements) {
        for (TypeSolver el : elements) {
            add(el);
        }
    }

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    public void add(TypeSolver typeSolver) {
        this.elements.add(typeSolver);
        typeSolver.setParent(this);
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        for (TypeSolver ts : elements) {
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
            throw new UnsolvedSymbolException(name);
        }
    }
}
