package com.github.javaparser.metamodel;

import java.util.Optional;

public class TryStmtMetaModel extends BaseNodeMetaModel {

    TryStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.TryStmt.class, "TryStmt", "com.github.javaparser.ast.stmt.TryStmt", "com.github.javaparser.ast.stmt", false);
    }
}

