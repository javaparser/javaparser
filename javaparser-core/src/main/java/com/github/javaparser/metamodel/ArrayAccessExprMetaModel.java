package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayAccessExprMetaModel extends ExpressionMetaModel {

    ArrayAccessExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.ArrayAccessExpr.class, "ArrayAccessExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel indexPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
