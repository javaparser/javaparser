package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThrowStmtMetaModel extends BaseNodeMetaModel {

    ThrowStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ThrowStmt.class, "ThrowStmt", "com.github.javaparser.ast.stmt.ThrowStmt", "com.github.javaparser.ast.stmt", false);
    }
}

