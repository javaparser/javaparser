package com.github.javaparser.metamodel;

import java.util.Optional;

public class WhileStmtMetaModel extends BaseNodeMetaModel {

    WhileStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.WhileStmt.class, "WhileStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel conditionPropertyMetaModel;
}

