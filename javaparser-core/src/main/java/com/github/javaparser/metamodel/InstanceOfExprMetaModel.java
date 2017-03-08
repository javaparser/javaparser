package com.github.javaparser.metamodel;

import java.util.Optional;

public class InstanceOfExprMetaModel extends ExpressionMetaModel {

    InstanceOfExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.InstanceOfExpr.class, "InstanceOfExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}
