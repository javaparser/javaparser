package com.github.javaparser.metamodel;

import java.util.Optional;

public class DoStmtMetaModel extends ClassMetaModel {

    public DoStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.stmt.DoStmt.class, "DoStmt", "com.github.javaparser.ast.stmt.DoStmt", "com.github.javaparser.ast.stmt", false);
    }
}

