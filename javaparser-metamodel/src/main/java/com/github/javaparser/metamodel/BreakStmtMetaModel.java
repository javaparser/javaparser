package com.github.javaparser.metamodel;

import java.util.Optional;

public class BreakStmtMetaModel extends BaseNodeMetaModel {

    BreakStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.BreakStmt.class, "BreakStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;
}

