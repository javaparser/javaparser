package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodCallExprMetaModel extends ClassMetaModel {

    public MethodCallExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.MethodCallExpr.class, "MethodCallExpr", "com.github.javaparser.ast.expr.MethodCallExpr", "com.github.javaparser.ast.expr", false);
    }
}

