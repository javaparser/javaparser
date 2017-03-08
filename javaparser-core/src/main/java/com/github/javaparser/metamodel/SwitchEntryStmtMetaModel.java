package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryStmtMetaModel extends StatementMetaModel {

    SwitchEntryStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;

    public PropertyMetaModel statementsPropertyMetaModel;
}
