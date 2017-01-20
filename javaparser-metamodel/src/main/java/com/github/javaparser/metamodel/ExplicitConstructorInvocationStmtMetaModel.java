package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExplicitConstructorInvocationStmtMetaModel extends ClassMetaModel {

    ExplicitConstructorInvocationStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt.class, "ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt", false);
    }
}

