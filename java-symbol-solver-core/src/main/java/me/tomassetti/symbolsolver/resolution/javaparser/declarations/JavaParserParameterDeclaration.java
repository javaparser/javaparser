package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.body.Parameter;
import me.tomassetti.symbolsolver.model.declarations.ParameterDeclaration;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;

public class JavaParserParameterDeclaration implements ParameterDeclaration {

    private Parameter wrappedNode;
    private TypeSolver typeSolver;

    public JavaParserParameterDeclaration(Parameter wrappedNode, TypeSolver typeSolver) {
        this.wrappedNode = wrappedNode;
        this.typeSolver = typeSolver;
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
    public TypeUsage getType() {
        return JavaParserFacade.get(typeSolver).convert(wrappedNode.getType(), wrappedNode);
    }
}
