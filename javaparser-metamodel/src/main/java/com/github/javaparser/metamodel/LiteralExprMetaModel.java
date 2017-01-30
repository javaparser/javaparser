package com.github.javaparser.metamodel;

import java.util.Optional;

public class LiteralExprMetaModel extends BaseNodeMetaModel {

    LiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.LiteralExpr.class, "LiteralExpr", "com.github.javaparser.ast.expr", true, false);
    }
}

