package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayInitializerExprMetaModel extends ExpressionMetaModel {

    ArrayInitializerExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.ArrayInitializerExpr.class, "ArrayInitializerExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel valuesPropertyMetaModel;
}
