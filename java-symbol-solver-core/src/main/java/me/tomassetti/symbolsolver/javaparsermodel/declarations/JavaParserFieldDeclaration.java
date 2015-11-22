package me.tomassetti.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsageImpl;
import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.javaparsermodel.JavaParserFacade;

public class JavaParserFieldDeclaration implements FieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration fieldDeclaration;
    private EnumConstantDeclaration enumConstantDeclaration;
    private TypeSolver typeSolver;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator, TypeSolver typeSolver) {
        this.variableDeclarator = variableDeclarator;
        this.typeSolver = typeSolver;
        if (!(variableDeclarator.getParentNode() instanceof com.github.javaparser.ast.body.FieldDeclaration)) {
            throw new IllegalStateException();
        }
        this.fieldDeclaration = (com.github.javaparser.ast.body.FieldDeclaration) variableDeclarator.getParentNode();
    }

    public JavaParserFieldDeclaration(EnumConstantDeclaration enumConstantDeclaration) {
        this.enumConstantDeclaration = enumConstantDeclaration;
    }

    @Override
    public TypeUsage getType() {
        if (enumConstantDeclaration != null) {
            com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = (com.github.javaparser.ast.body.EnumDeclaration) enumConstantDeclaration.getParentNode();
            return new ReferenceTypeUsageImpl(new JavaParserEnumDeclaration(enumDeclaration, typeSolver), typeSolver);
        } else {
            return JavaParserFacade.get(typeSolver).convert(fieldDeclaration.getType(), fieldDeclaration);
        }
    }

    @Override
    public String getName() {
        if (enumConstantDeclaration != null) {
            return enumConstantDeclaration.getName();
        } else {
            return variableDeclarator.getId().getName();
        }
    }

    @Override
    public boolean isField() {
        return true;
    }


}
