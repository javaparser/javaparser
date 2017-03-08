package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassExprMetaModel extends ExpressionMetaModel {

    ClassExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.ClassExpr.class, "ClassExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel typePropertyMetaModel;
}
