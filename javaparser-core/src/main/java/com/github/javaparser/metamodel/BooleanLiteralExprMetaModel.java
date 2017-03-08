package com.github.javaparser.metamodel;

import java.util.Optional;

public class BooleanLiteralExprMetaModel extends LiteralExprMetaModel {

    BooleanLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel valuePropertyMetaModel;
}
