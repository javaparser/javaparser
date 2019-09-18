package com.github.javaparser.metamodel;

import java.util.Optional;

public class TextBlockLiteralExprMetaModel extends LiteralStringValueExprMetaModel {

    TextBlockLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.TextBlockLiteralExpr.class, "TextBlockLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
