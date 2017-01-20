package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForStmtMetaModel extends BaseNodeMetaModel {

    ForStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt.ForStmt", "com.github.javaparser.ast.stmt", false);
    }
}

