package com.github.javaparser.metamodel;

import java.util.Optional;

public class SuperExprMetaModel extends ExpressionMetaModel {

    SuperExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.SuperExpr.class, "SuperExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel classExprPropertyMetaModel;
}
