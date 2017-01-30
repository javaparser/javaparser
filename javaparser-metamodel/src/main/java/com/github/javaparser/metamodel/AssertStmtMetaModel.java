package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssertStmtMetaModel extends BaseNodeMetaModel {

    AssertStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.AssertStmt.class, "AssertStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel checkPropertyMetaModel;

    public PropertyMetaModel messagePropertyMetaModel;
}

