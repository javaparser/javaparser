package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends ExpressionMetaModel {

    UnaryExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel operatorPropertyMetaModel;

    public PropertyMetaModel prefixPropertyMetaModel;

    public PropertyMetaModel postfixPropertyMetaModel;
}
