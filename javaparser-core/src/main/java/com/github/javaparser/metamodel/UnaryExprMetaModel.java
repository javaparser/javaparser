package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends BaseNodeMetaModel {

    UnaryExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel operatorPropertyMetaModel;
}

