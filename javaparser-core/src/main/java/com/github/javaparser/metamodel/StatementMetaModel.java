package com.github.javaparser.metamodel;

import java.util.Optional;

public class StatementMetaModel extends ClassMetaModel {

    public StatementMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.Statement.class, "Statement", "com.github.javaparser.ast.stmt.Statement", "com.github.javaparser.ast.stmt", true);
    }
}

