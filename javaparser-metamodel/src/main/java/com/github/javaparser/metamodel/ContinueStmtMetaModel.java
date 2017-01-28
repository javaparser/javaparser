package com.github.javaparser.metamodel;

import java.util.Optional;

public class ContinueStmtMetaModel extends BaseNodeMetaModel {

    ContinueStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ContinueStmt.class, "ContinueStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;
}

