package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryStmtMetaModel extends BaseNodeMetaModel {

    SwitchEntryStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt.SwitchEntryStmt", "com.github.javaparser.ast.stmt", false);
    }
}

