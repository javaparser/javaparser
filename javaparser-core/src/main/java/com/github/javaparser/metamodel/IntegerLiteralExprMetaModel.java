package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntegerLiteralExprMetaModel extends LiteralStringValueExprMetaModel {

    IntegerLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.IntegerLiteralExpr.class, "IntegerLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
