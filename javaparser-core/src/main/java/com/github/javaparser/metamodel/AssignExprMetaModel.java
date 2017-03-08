package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssignExprMetaModel extends ExpressionMetaModel {

    AssignExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel operatorPropertyMetaModel;

    public PropertyMetaModel targetPropertyMetaModel;

    public PropertyMetaModel valuePropertyMetaModel;
}
