package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends StatementMetaModel {

    LabeledStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel labelPropertyMetaModel;

    public PropertyMetaModel statementPropertyMetaModel;
}
