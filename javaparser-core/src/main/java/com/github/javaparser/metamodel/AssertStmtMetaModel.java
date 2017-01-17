package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssertStmtMetaModel extends ClassMetaModel {

    public AssertStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.AssertStmt.class, "AssertStmt", "com.github.javaparser.ast.stmt.AssertStmt", "com.github.javaparser.ast.stmt", false);
    }
}

