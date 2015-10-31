package me.tomassetti.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import me.tomassetti.symbolsolver.resolution.javaparser.JavaParserFacade;

import me.tomassetti.symbolsolver.model.declarations.FieldDeclaration;
import me.tomassetti.symbolsolver.resolution.TypeSolver;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;
import me.tomassetti.symbolsolver.model.typesystem.ReferenceTypeUsage;

public class JavaParserFieldDeclaration implements FieldDeclaration {

    private VariableDeclarator variableDeclarator;
    private com.github.javaparser.ast.body.FieldDeclaration fieldDeclaration;
    private EnumConstantDeclaration enumConstantDeclaration;

    public JavaParserFieldDeclaration(VariableDeclarator variableDeclarator) {
        this.variableDeclarator = variableDeclarator;
        if (!(variableDeclarator.getParentNode() instanceof com.github.javaparser.ast.body.FieldDeclaration)){
            throw new IllegalStateException();
        }
        this.fieldDeclaration = (com.github.javaparser.ast.body.FieldDeclaration)variableDeclarator.getParentNode();
    }

    public JavaParserFieldDeclaration(EnumConstantDeclaration enumConstantDeclaration) {
        this.enumConstantDeclaration = enumConstantDeclaration;
    }

    @Override
    public TypeUsage getType(TypeSolver typeSolver) {
        if (enumConstantDeclaration != null) {
            com.github.javaparser.ast.body.EnumDeclaration enumDeclaration = (com.github.javaparser.ast.body.EnumDeclaration)enumConstantDeclaration.getParentNode();
            return new ReferenceTypeUsage(new JavaParserEnumDeclaration(enumDeclaration, typeSolver), typeSolver);
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
