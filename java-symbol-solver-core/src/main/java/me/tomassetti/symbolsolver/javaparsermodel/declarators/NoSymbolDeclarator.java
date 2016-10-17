package me.tomassetti.symbolsolver.javaparsermodel.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;

public class NoSymbolDeclarator<N extends Node> extends AbstractSymbolDeclarator<N> {

    public NoSymbolDeclarator(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<ValueDeclaration> getSymbolDeclarations() {
        return Collections.emptyList();
    }

}
