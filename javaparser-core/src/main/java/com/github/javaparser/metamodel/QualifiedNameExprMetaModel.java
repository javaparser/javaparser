package com.github.javaparser.metamodel;

import java.util.Optional;

public class QualifiedNameExprMetaModel extends ExpressionMetaModel {

    QualifiedNameExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.QualifiedNameExpr.class, "QualifiedNameExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;
}
