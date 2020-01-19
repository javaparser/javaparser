package com.github.javaparser.metamodel;

import java.util.Optional;

public class StringLiteralExprMetaModel extends LiteralStringValueExprMetaModel {

    StringLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.StringLiteralExpr.class, "StringLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
