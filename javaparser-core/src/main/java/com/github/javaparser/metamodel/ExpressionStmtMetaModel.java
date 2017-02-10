package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionStmtMetaModel extends BaseNodeMetaModel {

    ExpressionStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ExpressionStmt.class, "ExpressionStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;
}

