package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockStmtMetaModel extends ClassMetaModel {

    public BlockStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.BlockStmt.class, "BlockStmt", "com.github.javaparser.ast.stmt.BlockStmt", "com.github.javaparser.ast.stmt", false);
    }
}

