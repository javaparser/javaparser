package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends BaseNodeMetaModel {

    IfStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt.IfStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel conditionPropertyMetaModel;

    public PropertyMetaModel elseStmtPropertyMetaModel;

    public PropertyMetaModel thenStmtPropertyMetaModel;
}

