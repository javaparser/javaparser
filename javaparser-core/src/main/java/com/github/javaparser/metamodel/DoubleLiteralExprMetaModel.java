package com.github.javaparser.metamodel;

import java.util.Optional;

public class DoubleLiteralExprMetaModel extends BaseNodeMetaModel {

    DoubleLiteralExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.DoubleLiteralExpr.class, "DoubleLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}

