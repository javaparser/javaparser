package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends StatementMetaModel {

    IfStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel conditionPropertyMetaModel;

    public PropertyMetaModel elseStmtPropertyMetaModel;

    public PropertyMetaModel thenStmtPropertyMetaModel;

    public PropertyMetaModel cascadingIfStmtPropertyMetaModel;

    public PropertyMetaModel elseBlockPropertyMetaModel;

    public PropertyMetaModel elseBranchPropertyMetaModel;

    public PropertyMetaModel thenBlockPropertyMetaModel;
}
