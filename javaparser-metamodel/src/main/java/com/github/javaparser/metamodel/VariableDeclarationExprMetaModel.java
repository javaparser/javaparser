package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclarationExprMetaModel extends BaseNodeMetaModel {

    VariableDeclarationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr.VariableDeclarationExpr", "com.github.javaparser.ast.expr", false);
    }
}

