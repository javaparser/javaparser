package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConditionalExprMetaModel extends BaseNodeMetaModel {

    ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel conditionPropertyMetaModel;

    public PropertyMetaModel elseExprPropertyMetaModel;

    public PropertyMetaModel thenExprPropertyMetaModel;
}

