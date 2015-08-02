package me.tomassetti.symbolsolver.model.javaparser.declarators;

import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
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
public class FieldSymbolDeclarator extends AbstractSymbolDeclarator<FieldDeclaration> {


    public FieldSymbolDeclarator(FieldDeclaration wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<SymbolDeclaration> getSymbolDeclarations() {
        List<SymbolDeclaration> symbols = new LinkedList<>();
        for (VariableDeclarator v : wrappedNode.getVariables()) {
            symbols.add(JavaParserSymbolDeclaration.field(v, typeSolver));
        }
        return symbols;
    }

    @Override
    public List<MethodDeclaration> getMethodDeclarations() {
        return Collections.emptyList();
    }
}
