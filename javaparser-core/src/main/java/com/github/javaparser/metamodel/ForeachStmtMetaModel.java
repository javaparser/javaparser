package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForeachStmtMetaModel extends ClassMetaModel {

    ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt.ForeachStmt", "com.github.javaparser.ast.stmt", false);
    }
}

