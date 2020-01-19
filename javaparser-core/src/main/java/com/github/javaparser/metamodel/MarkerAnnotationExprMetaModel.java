package com.github.javaparser.metamodel;

import java.util.Optional;

public class MarkerAnnotationExprMetaModel extends AnnotationExprMetaModel {

    MarkerAnnotationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.MarkerAnnotationExpr.class, "MarkerAnnotationExpr", "com.github.javaparser.ast.expr", false, false);
    }
}
