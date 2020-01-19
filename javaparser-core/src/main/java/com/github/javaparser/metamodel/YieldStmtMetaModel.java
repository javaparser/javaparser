package com.github.javaparser.metamodel;

import java.util.Optional;

public class YieldStmtMetaModel extends StatementMetaModel {

    YieldStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.YieldStmt.class, "YieldStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel expressionPropertyMetaModel;
}
