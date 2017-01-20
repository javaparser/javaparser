package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodCallExprMetaModel extends BaseNodeMetaModel {

    MethodCallExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodCallExpr.class, "MethodCallExpr", "com.github.javaparser.ast.expr.MethodCallExpr", "com.github.javaparser.ast.expr", false);
    }
}

