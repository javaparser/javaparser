package me.tomassetti.symbolsolver.resolution.javaparser.declarators;

import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.declarations.JavaParserSymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by federico on 28/07/15.
 */
public class VariableSymbolDeclarator extends AbstractSymbolDeclarator<VariableDeclarationExpr> {


    public VariableSymbolDeclarator(VariableDeclarationExpr wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<ValueDeclaration> getSymbolDeclarations() {
        List<ValueDeclaration> symbols = wrappedNode.getVars().stream().map(
                v -> JavaParserSymbolDeclaration.field(v, typeSolver)
        ).collect(
                Collectors.toCollection(() -> new LinkedList<>()));
        return symbols;
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
