package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnparsableStmtMetaModel extends StatementMetaModel {

    UnparsableStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.UnparsableStmt.class, "UnparsableStmt", "com.github.javaparser.ast.stmt", false, false);
    }
}
