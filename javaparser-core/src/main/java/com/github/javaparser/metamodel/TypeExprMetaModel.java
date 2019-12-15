package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeExprMetaModel extends ExpressionMetaModel {

    TypeExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.TypeExpr.class, "TypeExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel typePropertyMetaModel;
}
