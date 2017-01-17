package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReturnStmtMetaModel extends ClassMetaModel {

    public ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ReturnStmt.class, "ReturnStmt", "com.github.javaparser.ast.stmt.ReturnStmt", "com.github.javaparser.ast.stmt", false);
    }
}

