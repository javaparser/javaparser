package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThisExprMetaModel extends ExpressionMetaModel {

    ThisExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.ThisExpr.class, "ThisExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel classExprPropertyMetaModel;
}
