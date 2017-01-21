package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForeachStmtMetaModel extends BaseNodeMetaModel {

    ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel iterablePropertyMetaModel;

    public PropertyMetaModel variablePropertyMetaModel;
}

