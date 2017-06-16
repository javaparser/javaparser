package com.github.javaparser.metamodel;

import java.util.Optional;

public class LongLiteralExprMetaModel extends LiteralStringValueExprMetaModel {

    LongLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
