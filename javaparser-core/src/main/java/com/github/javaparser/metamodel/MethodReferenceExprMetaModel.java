package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodReferenceExprMetaModel extends ClassMetaModel {

    public MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr.MethodReferenceExpr", "com.github.javaparser.ast.expr", false);
    }
}

