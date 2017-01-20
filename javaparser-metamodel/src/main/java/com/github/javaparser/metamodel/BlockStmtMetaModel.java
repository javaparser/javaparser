package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockStmtMetaModel extends BaseNodeMetaModel {

    BlockStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt.BlockStmt", "com.github.javaparser.ast.stmt", false);
    }
}

