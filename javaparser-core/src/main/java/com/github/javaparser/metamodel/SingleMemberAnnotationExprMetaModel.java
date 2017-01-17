package com.github.javaparser.metamodel;

import java.util.Optional;

public class SingleMemberAnnotationExprMetaModel extends ClassMetaModel {

    public SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr.SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

