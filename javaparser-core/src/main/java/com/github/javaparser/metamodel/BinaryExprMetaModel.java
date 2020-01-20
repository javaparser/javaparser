package com.github.javaparser.metamodel;

import java.util.Optional;

public class BinaryExprMetaModel extends ExpressionMetaModel {

    BinaryExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.BinaryExpr.class, "BinaryExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel leftPropertyMetaModel;

    public PropertyMetaModel operatorPropertyMetaModel;

    public PropertyMetaModel rightPropertyMetaModel;
}
