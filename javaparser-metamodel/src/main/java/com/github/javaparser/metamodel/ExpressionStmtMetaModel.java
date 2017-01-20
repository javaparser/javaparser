package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionStmtMetaModel extends BaseNodeMetaModel {

    ExpressionStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ExpressionStmt.class, "ExpressionStmt", "com.github.javaparser.ast.stmt.ExpressionStmt", "com.github.javaparser.ast.stmt", false);
    }
}

