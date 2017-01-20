package com.github.javaparser.metamodel;

import java.util.Optional;

public class NormalAnnotationExprMetaModel extends ClassMetaModel {

    NormalAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NormalAnnotationExpr.class, "NormalAnnotationExpr", "com.github.javaparser.ast.expr.NormalAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

