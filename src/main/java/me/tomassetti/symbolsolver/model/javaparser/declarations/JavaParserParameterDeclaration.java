package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.Parameter;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;

/**
 * Created by federico on 02/08/15.
 */
public class JavaParserParameterDeclaration implements ParameterDeclaration {

    private Parameter wrappedNode;

    public JavaParserParameterDeclaration(Parameter wrappedNode) {
        this.wrappedNode = wrappedNode;
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isField() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isParameter() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isType() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeUsage getType(TypeSolver typeSolver) {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
    }
}
