package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationExprMetaModel extends BaseNodeMetaModel {

    AnnotationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AnnotationExpr.class, "AnnotationExpr", "com.github.javaparser.ast.expr.AnnotationExpr", "com.github.javaparser.ast.expr", true);
    }
}

