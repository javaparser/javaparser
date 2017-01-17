package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThrowStmtMetaModel extends ClassMetaModel {

    public ThrowStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ThrowStmt.class, "ThrowStmt", "com.github.javaparser.ast.stmt.ThrowStmt", "com.github.javaparser.ast.stmt", false);
    }
}

