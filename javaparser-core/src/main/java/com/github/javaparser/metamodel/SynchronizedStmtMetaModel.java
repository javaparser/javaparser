package com.github.javaparser.metamodel;

import java.util.Optional;

public class SynchronizedStmtMetaModel extends ClassMetaModel {

    public SynchronizedStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.SynchronizedStmt.class, "SynchronizedStmt", "com.github.javaparser.ast.stmt.SynchronizedStmt", "com.github.javaparser.ast.stmt", false);
    }
}

