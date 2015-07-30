package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.MethodDeclaration;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class ParameterSymbolDeclarator extends AbstractSymbolDeclarator<Parameter> {


    public ParameterSymbolDeclarator(Parameter wrappedNode) {
        super(wrappedNode);
    }

    @Override
    public List<SymbolDeclaration> getSymbolDeclarations() {
        List<SymbolDeclaration> symbols = new LinkedList<>();
        symbols.add(JavaParserSymbolDeclaration.parameter(wrappedNode));
        return symbols;
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
