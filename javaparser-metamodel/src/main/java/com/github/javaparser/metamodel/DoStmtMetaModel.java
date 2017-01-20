package com.github.javaparser.metamodel;

import java.util.Optional;

public class DoStmtMetaModel extends BaseNodeMetaModel {

    DoStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.DoStmt.class, "DoStmt", "com.github.javaparser.ast.stmt.DoStmt", "com.github.javaparser.ast.stmt", false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel conditionPropertyMetaModel;
}

