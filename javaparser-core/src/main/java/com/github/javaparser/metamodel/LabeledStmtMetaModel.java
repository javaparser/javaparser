package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends ClassMetaModel {

    public LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
    }
}

