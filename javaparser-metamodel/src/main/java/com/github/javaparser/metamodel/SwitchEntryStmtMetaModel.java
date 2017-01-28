package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryStmtMetaModel extends BaseNodeMetaModel {

    SwitchEntryStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;

    public PropertyMetaModel statementsPropertyMetaModel;
}

