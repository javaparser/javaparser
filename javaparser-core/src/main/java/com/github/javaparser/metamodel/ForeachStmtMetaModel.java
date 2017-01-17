package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForeachStmtMetaModel extends ClassMetaModel {

    public ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt.ForeachStmt", "com.github.javaparser.ast.stmt", false);
    }
}

