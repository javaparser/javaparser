package com.github.javaparser.metamodel;

import java.util.Optional;

public class StatementMetaModel extends BaseNodeMetaModel {

    StatementMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.Statement.class, "Statement", "com.github.javaparser.ast.stmt", true);
    }
}

