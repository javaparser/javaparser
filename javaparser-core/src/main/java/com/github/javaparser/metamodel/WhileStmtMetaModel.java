package com.github.javaparser.metamodel;

import java.util.Optional;

public class WhileStmtMetaModel extends StatementMetaModel {

    WhileStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.WhileStmt.class, "WhileStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel conditionPropertyMetaModel;
}
