package me.tomassetti.symbolsolver.model.typesolvers;

import me.tomassetti.symbolsolver.model.SymbolReference;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by federico on 30/07/15.
 */
public class DummyTypeSolver implements TypeSolver {

    private Map<String, TypeDeclaration> declarationMap = new HashMap<>();

    public void addDeclaration(String name, TypeDeclaration typeDeclaration){
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
