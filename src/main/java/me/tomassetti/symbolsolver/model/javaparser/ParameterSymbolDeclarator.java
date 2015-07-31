package me.tomassetti.symbolsolver.model.javaparser;

import com.github.javaparser.ast.body.Parameter;
import me.tomassetti.symbolsolver.model.MethodDeclaration;
import me.tomassetti.symbolsolver.model.SymbolDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.javaparser.declarations.JavaParserSymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by federico on 28/07/15.
 */
public class ParameterSymbolDeclarator extends AbstractSymbolDeclarator<Parameter> {


    public ParameterSymbolDeclarator(Parameter wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<SymbolDeclaration> getSymbolDeclarations() {
        List<SymbolDeclaration> symbols = new LinkedList<>();
        symbols.add(JavaParserSymbolDeclaration.parameter(wrappedNode, typeSolver));
        return symbols;
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
