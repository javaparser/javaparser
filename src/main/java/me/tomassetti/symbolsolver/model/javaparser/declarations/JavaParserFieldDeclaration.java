package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;

/**
 * Created by federico on 04/08/15.
 */
public class JavaParserFieldDeclaration implements FieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration fieldDeclaration;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator) {
        this.variableDeclarator = variableDeclarator;
        if (!(variableDeclarator.getParentNode() instanceof com.github.javaparser.ast.body.FieldDeclaration)){
            throw new IllegalStateException();
        }
        this.fieldDeclaration = (com.github.javaparser.ast.body.FieldDeclaration)variableDeclarator.getParentNode();
    }

    @Override
    public TypeDeclaration asTypeDeclaration() {
        throw new UnsupportedOperationException();
    }

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        return new JavaParserFacade(typeSolver).convert(fieldDeclaration.getType(), fieldDeclaration);
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
}
