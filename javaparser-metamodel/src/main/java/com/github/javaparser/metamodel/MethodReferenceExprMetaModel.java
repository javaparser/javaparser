package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodReferenceExprMetaModel extends BaseNodeMetaModel {

    MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel identifierPropertyMetaModel;

    public PropertyMetaModel scopePropertyMetaModel;

    public PropertyMetaModel typeArgumentsPropertyMetaModel;
}

