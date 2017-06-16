package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclarationExprMetaModel extends ExpressionMetaModel {

    VariableDeclarationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel variablesPropertyMetaModel;

    public PropertyMetaModel maximumCommonTypePropertyMetaModel;
}
