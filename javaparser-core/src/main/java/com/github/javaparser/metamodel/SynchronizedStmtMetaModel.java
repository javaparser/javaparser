package com.github.javaparser.metamodel;

import java.util.Optional;

public class SynchronizedStmtMetaModel extends StatementMetaModel {

    SynchronizedStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.SynchronizedStmt.class, "SynchronizedStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel expressionPropertyMetaModel;
}
