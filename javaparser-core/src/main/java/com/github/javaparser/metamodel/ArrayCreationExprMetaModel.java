package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationExprMetaModel extends ExpressionMetaModel {

    ArrayCreationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel elementTypePropertyMetaModel;

    public PropertyMetaModel initializerPropertyMetaModel;

    public PropertyMetaModel levelsPropertyMetaModel;
}
