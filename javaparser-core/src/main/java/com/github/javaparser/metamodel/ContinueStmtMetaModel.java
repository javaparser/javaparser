package com.github.javaparser.metamodel;

import java.util.Optional;

public class ContinueStmtMetaModel extends ClassMetaModel {

    public ContinueStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ContinueStmt.class, "ContinueStmt", "com.github.javaparser.ast.stmt.ContinueStmt", "com.github.javaparser.ast.stmt", false);
    }
}

