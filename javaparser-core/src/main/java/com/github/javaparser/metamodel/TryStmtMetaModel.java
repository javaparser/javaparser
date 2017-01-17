package com.github.javaparser.metamodel;

import java.util.Optional;

public class TryStmtMetaModel extends ClassMetaModel {

    public TryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.TryStmt.class, "TryStmt", "com.github.javaparser.ast.stmt.TryStmt", "com.github.javaparser.ast.stmt", false);
    }
}

