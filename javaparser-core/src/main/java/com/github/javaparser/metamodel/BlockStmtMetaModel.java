package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockStmtMetaModel extends StatementMetaModel {

    BlockStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel statementsPropertyMetaModel;
}
