package me.tomassetti.symbolsolver.javaparsermodel.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.SymbolDeclarator;

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
