package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForeachStmtMetaModel extends StatementMetaModel {

    ForeachStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel iterablePropertyMetaModel;

    public PropertyMetaModel variablePropertyMetaModel;
}
