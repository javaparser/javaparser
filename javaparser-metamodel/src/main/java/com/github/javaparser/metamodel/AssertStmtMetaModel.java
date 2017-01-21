package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssertStmtMetaModel extends BaseNodeMetaModel {

    AssertStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.AssertStmt.class, "AssertStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel checkPropertyMetaModel;

    public PropertyMetaModel messagePropertyMetaModel;
}

