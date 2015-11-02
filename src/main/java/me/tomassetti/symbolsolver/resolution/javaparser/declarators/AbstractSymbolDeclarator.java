package me.tomassetti.symbolsolver.resolution.javaparser.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

/**
 * @author Federico Tomassetti
 */
public abstract class AbstractSymbolDeclarator<N extends Node> implements SymbolDeclarator {

    protected N wrappedNode;
    protected TypeSolver typeSolver;
    public AbstractSymbolDeclarator(N wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
    }
}
