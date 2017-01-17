package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionStmtMetaModel extends ClassMetaModel {

    public ExpressionStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ExpressionStmt.class, "ExpressionStmt", "com.github.javaparser.ast.stmt.ExpressionStmt", "com.github.javaparser.ast.stmt", false);
    }
}

