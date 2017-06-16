package com.github.javaparser.metamodel;

import java.util.Optional;

public class TryStmtMetaModel extends StatementMetaModel {

    TryStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.TryStmt.class, "TryStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel catchClausesPropertyMetaModel;

    public PropertyMetaModel finallyBlockPropertyMetaModel;

    public PropertyMetaModel resourcesPropertyMetaModel;

    public PropertyMetaModel tryBlockPropertyMetaModel;
}
