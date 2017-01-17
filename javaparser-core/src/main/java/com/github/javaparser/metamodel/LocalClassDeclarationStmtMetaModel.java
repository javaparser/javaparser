package com.github.javaparser.metamodel;

import java.util.Optional;

public class LocalClassDeclarationStmtMetaModel extends ClassMetaModel {

    public LocalClassDeclarationStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.LocalClassDeclarationStmt.class, "LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt.LocalClassDeclarationStmt", "com.github.javaparser.ast.stmt", false);
    }
}

