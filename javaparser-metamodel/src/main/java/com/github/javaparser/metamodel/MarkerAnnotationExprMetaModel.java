package com.github.javaparser.metamodel;

import java.util.Optional;

public class MarkerAnnotationExprMetaModel extends ClassMetaModel {

    MarkerAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MarkerAnnotationExpr.class, "MarkerAnnotationExpr", "com.github.javaparser.ast.expr.MarkerAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

