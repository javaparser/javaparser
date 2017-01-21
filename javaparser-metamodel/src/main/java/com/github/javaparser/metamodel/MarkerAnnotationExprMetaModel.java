package com.github.javaparser.metamodel;

import java.util.Optional;

public class MarkerAnnotationExprMetaModel extends BaseNodeMetaModel {

    MarkerAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.MarkerAnnotationExpr.class, "MarkerAnnotationExpr", "com.github.javaparser.ast.expr", false, false);
    }
}

