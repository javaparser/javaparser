package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends BaseNodeMetaModel {

    LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
    }
}

