package com.github.javaparser.metamodel;

import java.util.Optional;

public class CastExprMetaModel extends BaseNodeMetaModel {

    CastExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.CastExpr.class, "CastExpr", "com.github.javaparser.ast.expr.CastExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}

