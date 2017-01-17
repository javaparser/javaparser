package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyStmtMetaModel extends ClassMetaModel {

    public EmptyStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.EmptyStmt.class, "EmptyStmt", "com.github.javaparser.ast.stmt.EmptyStmt", "com.github.javaparser.ast.stmt", false);
    }
}

