package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReturnStmtMetaModel extends BaseNodeMetaModel {

    ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ReturnStmt.class, "ReturnStmt", "com.github.javaparser.ast.stmt.ReturnStmt", "com.github.javaparser.ast.stmt", false);
    }
}

