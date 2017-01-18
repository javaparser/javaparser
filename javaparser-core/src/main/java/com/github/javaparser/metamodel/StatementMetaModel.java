package com.github.javaparser.metamodel;

import java.util.Optional;

public class StatementMetaModel extends ClassMetaModel {

    StatementMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.Statement.class, "Statement", "com.github.javaparser.ast.stmt.Statement", "com.github.javaparser.ast.stmt", true);
    }
}

