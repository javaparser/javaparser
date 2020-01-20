package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnclosedExprMetaModel extends ExpressionMetaModel {

    EnclosedExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.EnclosedExpr.class, "EnclosedExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel innerPropertyMetaModel;
}
