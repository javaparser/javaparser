package me.tomassetti.symbolsolver.model.javaparser.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.SymbolDeclarator;
import me.tomassetti.symbolsolver.model.TypeSolver;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractSymbolDeclarator<N extends Node> implements SymbolDeclarator {

    public AbstractSymbolDeclarator(N wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }

    protected N wrappedNode;
    protected TypeSolver typeSolver;
}
