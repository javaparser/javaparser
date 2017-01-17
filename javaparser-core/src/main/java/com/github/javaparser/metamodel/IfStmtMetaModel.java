package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends ClassMetaModel {

    public IfStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt.IfStmt", "com.github.javaparser.ast.stmt", false);
    }
}

