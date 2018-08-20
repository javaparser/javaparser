package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForEachStmtMetaModel extends StatementMetaModel {

    ForEachStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ForEachStmt.class, "ForEachStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel iterablePropertyMetaModel;

    public PropertyMetaModel variablePropertyMetaModel;
}
