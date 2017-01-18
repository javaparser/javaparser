package com.github.javaparser.metamodel;

import java.util.Optional;

public class WhileStmtMetaModel extends ClassMetaModel {

    WhileStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.WhileStmt.class, "WhileStmt", "com.github.javaparser.ast.stmt.WhileStmt", "com.github.javaparser.ast.stmt", false);
    }
}

