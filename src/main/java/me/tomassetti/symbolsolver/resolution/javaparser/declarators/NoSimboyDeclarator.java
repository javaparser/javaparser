package me.tomassetti.symbolsolver.resolution.javaparser.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;

import java.util.Collections;
import java.util.List;

/**
 * Created by federico on 23/08/15.
 */
public class NoSimboyDeclarator<N extends Node> extends AbstractSymbolDeclarator<N> {

    public NoSimboyDeclarator(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<ValueDeclaration> getSymbolDeclarations() {
        return Collections.emptyList();
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
