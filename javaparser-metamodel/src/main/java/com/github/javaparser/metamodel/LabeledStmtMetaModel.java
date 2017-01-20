package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends BaseNodeMetaModel {

    LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.LabeledStmt.class, "LabeledStmt", "com.github.javaparser.ast.stmt.LabeledStmt", "com.github.javaparser.ast.stmt", false);
    }
}

