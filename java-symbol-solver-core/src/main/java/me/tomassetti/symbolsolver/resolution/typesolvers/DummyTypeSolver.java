package me.tomassetti.symbolsolver.resolution.typesolvers;

import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.HashMap;
import java.util.Map;

public class DummyTypeSolver implements TypeSolver {

    private TypeSolver parent;
    private Map<String, TypeDeclaration> declarationMap = new HashMap<>();

    @Override
    public TypeSolver getParent() {
        return parent;
    }

    @Override
    public void setParent(TypeSolver parent) {
        this.parent = parent;
    }

    public void addDeclaration(String name, TypeDeclaration typeDeclaration) {
        this.declarationMap.put(name, typeDeclaration);
    }

    @Override
    public SymbolReference<TypeDeclaration> tryToSolveType(String name) {
        if (declarationMap.containsKey(name)) {
            return SymbolReference.solved(declarationMap.get(name));
        } else {
            return SymbolReference.unsolved(TypeDeclaration.class);
        }
    }

}
