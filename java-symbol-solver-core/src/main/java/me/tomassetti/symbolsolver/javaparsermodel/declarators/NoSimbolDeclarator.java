package me.tomassetti.symbolsolver.javaparsermodel.declarators;

import com.github.javaparser.ast.Node;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.List;

public class NoSimbolDeclarator<N extends Node> extends AbstractSymbolDeclarator<N> {

    public NoSimbolDeclarator(N wrappedNode, TypeSolver typeSolver) {
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
