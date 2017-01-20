package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchStmtMetaModel extends BaseNodeMetaModel {

    SwitchStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.SwitchStmt.class, "SwitchStmt", "com.github.javaparser.ast.stmt.SwitchStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel entriesPropertyMetaModel;

    public PropertyMetaModel selectorPropertyMetaModel;
}

