package com.github.javaparser.metamodel;

import com.github.javaparser.ast.stmt.UnparsableStmt;

import java.util.Optional;

public class UnparsableStatementMetaModel extends StatementMetaModel {

    UnparsableStatementMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, UnparsableStmt.class, "UnparsableStatement", "com.github.javaparser.ast.stmt", false, false);
    }
}
