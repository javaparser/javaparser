package com.github.javaparser.metamodel;

import java.util.Optional;

public class NormalAnnotationExprMetaModel extends ClassMetaModel {

    public NormalAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.NormalAnnotationExpr.class, "NormalAnnotationExpr", "com.github.javaparser.ast.expr.NormalAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

