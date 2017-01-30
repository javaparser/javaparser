package com.github.javaparser.metamodel;

import java.util.Optional;

public class LocalClassDeclarationStmtMetaModel extends BaseNodeMetaModel {

    LocalClassDeclarationStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.LocalClassDeclarationStmt.class, "LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel classDeclarationPropertyMetaModel;
}

