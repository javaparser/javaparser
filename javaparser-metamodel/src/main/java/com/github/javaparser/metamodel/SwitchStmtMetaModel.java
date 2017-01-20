package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchStmtMetaModel extends ClassMetaModel {

    SwitchStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SwitchStmt.class, "SwitchStmt", "com.github.javaparser.ast.stmt.SwitchStmt", "com.github.javaparser.ast.stmt", false);
    }
}

