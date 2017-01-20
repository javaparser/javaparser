package com.github.javaparser.metamodel;

import java.util.Optional;

public class BreakStmtMetaModel extends BaseNodeMetaModel {

    BreakStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.BreakStmt.class, "BreakStmt", "com.github.javaparser.ast.stmt.BreakStmt", "com.github.javaparser.ast.stmt", false);
    }
}

