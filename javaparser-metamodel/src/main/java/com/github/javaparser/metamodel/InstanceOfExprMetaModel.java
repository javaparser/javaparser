package com.github.javaparser.metamodel;

import java.util.Optional;

public class InstanceOfExprMetaModel extends BaseNodeMetaModel {

    InstanceOfExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.InstanceOfExpr.class, "InstanceOfExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}

