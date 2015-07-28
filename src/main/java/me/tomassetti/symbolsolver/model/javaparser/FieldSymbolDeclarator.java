package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.MethodDeclaration;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class FieldSymbolDeclarator extends AbstractSymbolDeclarator<FieldDeclaration> {


    public FieldSymbolDeclarator(FieldDeclaration wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public List<SymbolDeclaration> getSymbolDeclarations() {
        List<SymbolDeclaration> symbols = new LinkedList<>();
        for (VariableDeclarator v : wrappedNode.getVariables()) {
            symbols.add(JavaParserSymbolDeclaration.field(v));
        }
        return symbols;
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
