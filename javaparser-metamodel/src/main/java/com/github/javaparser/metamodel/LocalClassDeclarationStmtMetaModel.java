package com.github.javaparser.metamodel;

import java.util.Optional;

public class LocalClassDeclarationStmtMetaModel extends BaseNodeMetaModel {

    LocalClassDeclarationStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LocalClassDeclarationStmt.class, "LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt.LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt", false);
    }
}

