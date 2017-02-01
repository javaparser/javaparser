package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationExprMetaModel extends BaseNodeMetaModel {

    AnnotationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.AnnotationExpr.class, "AnnotationExpr", "com.github.javaparser.ast.expr", true, false);
    }

    public PropertyMetaModel namePropertyMetaModel;
}

