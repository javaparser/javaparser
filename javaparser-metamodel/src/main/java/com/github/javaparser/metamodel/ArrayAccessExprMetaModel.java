package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayAccessExprMetaModel extends BaseNodeMetaModel {

    ArrayAccessExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.ArrayAccessExpr.class, "ArrayAccessExpr", "com.github.javaparser.ast.expr.ArrayAccessExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel indexPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}

