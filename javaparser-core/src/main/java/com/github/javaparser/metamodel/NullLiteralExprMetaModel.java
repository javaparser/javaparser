package com.github.javaparser.metamodel;

import java.util.Optional;

public class NullLiteralExprMetaModel extends LiteralExprMetaModel {

    NullLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.NullLiteralExpr.class, "NullLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
