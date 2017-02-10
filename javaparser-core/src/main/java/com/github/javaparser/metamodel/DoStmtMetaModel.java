package com.github.javaparser.metamodel;

import java.util.Optional;

public class DoStmtMetaModel extends BaseNodeMetaModel {

    DoStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.DoStmt.class, "DoStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel conditionPropertyMetaModel;
}

