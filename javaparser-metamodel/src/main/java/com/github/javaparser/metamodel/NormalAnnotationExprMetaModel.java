package com.github.javaparser.metamodel;

import java.util.Optional;

public class NormalAnnotationExprMetaModel extends BaseNodeMetaModel {

    NormalAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.NormalAnnotationExpr.class, "NormalAnnotationExpr", "com.github.javaparser.ast.expr.NormalAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

