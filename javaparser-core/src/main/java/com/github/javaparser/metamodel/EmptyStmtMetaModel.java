package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyStmtMetaModel extends BaseNodeMetaModel {

    EmptyStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.EmptyStmt.class, "EmptyStmt", "com.github.javaparser.ast.stmt", false, false);
    }
}

