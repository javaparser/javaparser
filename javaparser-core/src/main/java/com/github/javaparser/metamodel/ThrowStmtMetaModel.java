package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThrowStmtMetaModel extends StatementMetaModel {

    ThrowStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ThrowStmt.class, "ThrowStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;
}
