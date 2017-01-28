package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnclosedExprMetaModel extends BaseNodeMetaModel {

    EnclosedExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.EnclosedExpr.class, "EnclosedExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel innerPropertyMetaModel;
}

