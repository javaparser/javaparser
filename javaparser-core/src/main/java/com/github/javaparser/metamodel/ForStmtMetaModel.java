package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForStmtMetaModel extends ClassMetaModel {

    public ForStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt.ForStmt", "com.github.javaparser.ast.stmt", false);
    }
}

