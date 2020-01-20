package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchStmtMetaModel extends StatementMetaModel {

    SwitchStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.SwitchStmt.class, "SwitchStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel entriesPropertyMetaModel;

    public PropertyMetaModel selectorPropertyMetaModel;
}
