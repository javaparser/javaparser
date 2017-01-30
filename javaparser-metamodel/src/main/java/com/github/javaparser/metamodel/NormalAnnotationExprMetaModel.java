package com.github.javaparser.metamodel;

import java.util.Optional;

public class NormalAnnotationExprMetaModel extends BaseNodeMetaModel {

    NormalAnnotationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.NormalAnnotationExpr.class, "NormalAnnotationExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel pairsPropertyMetaModel;
}

