package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends BaseNodeMetaModel {

    IfStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt.IfStmt", "com.github.javaparser.ast.stmt", false);
    }
}

