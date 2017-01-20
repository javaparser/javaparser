package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodReferenceExprMetaModel extends BaseNodeMetaModel {

    MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr.MethodReferenceExpr", "com.github.javaparser.ast.expr", false);
    }
}

