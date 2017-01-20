package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends ClassMetaModel {

    LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
    }
}

