package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionMetaModel extends BaseNodeMetaModel {

    ExpressionMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.Expression.class, "Expression", "com.github.javaparser.ast.expr", true, false);
    }
}

