package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReturnStmtMetaModel extends BaseNodeMetaModel {

    ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ReturnStmt.class, "ReturnStmt", "com.github.javaparser.ast.stmt.ReturnStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;
}

