package com.github.javaparser.metamodel;

import java.util.Optional;

public class SynchronizedStmtMetaModel extends BaseNodeMetaModel {

    SynchronizedStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.SynchronizedStmt.class, "SynchronizedStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel expressionPropertyMetaModel;
}

