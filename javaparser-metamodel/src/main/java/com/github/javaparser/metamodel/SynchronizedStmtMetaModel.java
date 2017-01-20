package com.github.javaparser.metamodel;

import java.util.Optional;

public class SynchronizedStmtMetaModel extends BaseNodeMetaModel {

    SynchronizedStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SynchronizedStmt.class, "SynchronizedStmt", "com.github.javaparser.ast.stmt.SynchronizedStmt", "com.github.javaparser.ast.stmt", false);
    }
}

