package me.tomassetti.symbolsolver.model.javaparser.declarations;

import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.JavaParserFacade;
import me.tomassetti.symbolsolver.model.FieldDeclaration;
import me.tomassetti.symbolsolver.model.TypeParameter;
import me.tomassetti.symbolsolver.model.TypeSolver;
import me.tomassetti.symbolsolver.model.declarations.TypeDeclaration;
import me.tomassetti.symbolsolver.model.usages.TypeUsage;
import me.tomassetti.symbolsolver.model.usages.TypeUsageOfTypeDeclaration;

import java.util.Optional;

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
    public TypeUsage getTypeUsage(TypeSolver typeSolver) {
        return JavaParserFacade.get(typeSolver).convertToUsage(fieldDeclaration.getType(), fieldDeclaration);
    }

    @Override
    public TypeDeclaration getType(TypeSolver typeSolver) {
        return JavaParserFacade.get(typeSolver).convert(fieldDeclaration.getType(), fieldDeclaration);
    }

    @Override
    public String getName() {
        return variableDeclarator.getId().getName();
    }

    @Override
    public boolean isField() {
        return true;
    }

    @Override
    public boolean isParameter() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isType() {
        return false;
    }

    @Override
    public boolean isClass() {
        return false;
    }

    @Override
    public boolean isInterface() {
        return false;
    }
}
