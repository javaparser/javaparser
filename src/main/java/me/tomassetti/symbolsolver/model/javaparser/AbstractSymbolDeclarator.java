package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;
import me.tomassetti.symbolsolver.model.SymbolDeclarator;

/**
 * Created by federico on 28/07/15.
 */
public abstract class AbstractSymbolDeclarator<N extends Node> implements SymbolDeclarator {

    public AbstractSymbolDeclarator(N wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    protected N wrappedNode;
}
