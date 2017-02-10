package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameExprMetaModel extends BaseNodeMetaModel {

    NameExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.NameExpr.class, "NameExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;
}

