package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclarationExprMetaModel extends ClassMetaModel {

    public VariableDeclarationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr.VariableDeclarationExpr", "com.github.javaparser.ast.expr", false);
    }
}

