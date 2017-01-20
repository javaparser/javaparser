package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockStmtMetaModel extends BaseNodeMetaModel {

    BlockStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt.BlockStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel statementsPropertyMetaModel;
}

