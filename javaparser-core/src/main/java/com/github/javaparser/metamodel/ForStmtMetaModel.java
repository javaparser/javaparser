package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForStmtMetaModel extends StatementMetaModel {

    ForStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel comparePropertyMetaModel;

    public PropertyMetaModel initializationPropertyMetaModel;

    public PropertyMetaModel updatePropertyMetaModel;
}
