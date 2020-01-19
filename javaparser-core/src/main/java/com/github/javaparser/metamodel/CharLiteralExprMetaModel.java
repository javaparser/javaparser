package com.github.javaparser.metamodel;

import java.util.Optional;

public class CharLiteralExprMetaModel extends LiteralStringValueExprMetaModel {

    CharLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.CharLiteralExpr.class, "CharLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
