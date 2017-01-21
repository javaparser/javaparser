package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationExprMetaModel extends BaseNodeMetaModel {

    ArrayCreationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.ArrayCreationExpr.class, "ArrayCreationExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel elementTypePropertyMetaModel;

    public PropertyMetaModel initializerPropertyMetaModel;

    public PropertyMetaModel levelsPropertyMetaModel;
}

