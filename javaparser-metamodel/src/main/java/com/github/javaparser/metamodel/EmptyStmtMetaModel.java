package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyStmtMetaModel extends BaseNodeMetaModel {

    EmptyStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.EmptyStmt.class, "EmptyStmt", "com.github.javaparser.ast.stmt", false, false);
    }
}

