package com.github.javaparser.metamodel;

import java.util.Optional;

public class ForStmtMetaModel extends ClassMetaModel {

    ForStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForStmt.class, "ForStmt", "com.github.javaparser.ast.stmt.ForStmt", "com.github.javaparser.ast.stmt", false);
    }
}

