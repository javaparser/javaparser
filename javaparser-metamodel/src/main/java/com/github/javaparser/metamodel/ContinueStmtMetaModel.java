package com.github.javaparser.metamodel;

import java.util.Optional;

public class ContinueStmtMetaModel extends ClassMetaModel {

    ContinueStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ContinueStmt.class, "ContinueStmt", "com.github.javaparser.ast.stmt.ContinueStmt", "com.github.javaparser.ast.stmt", false);
    }
}

