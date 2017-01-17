package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchEntryStmtMetaModel extends ClassMetaModel {

    public SwitchEntryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.SwitchEntryStmt.class, "SwitchEntryStmt", "com.github.javaparser.ast.stmt.SwitchEntryStmt", "com.github.javaparser.ast.stmt", false);
    }
}

