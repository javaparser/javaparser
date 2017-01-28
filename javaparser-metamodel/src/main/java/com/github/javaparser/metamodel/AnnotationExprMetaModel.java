package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationExprMetaModel extends BaseNodeMetaModel {

    AnnotationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.AnnotationExpr.class, "AnnotationExpr", "com.github.javaparser.ast.expr", true, false);
    }

    public PropertyMetaModel namePropertyMetaModel;
}

