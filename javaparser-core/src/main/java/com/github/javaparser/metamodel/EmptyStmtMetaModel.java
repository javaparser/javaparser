package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class EmptyStmtMetaModel extends ClassMetaModel {

    EmptyStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.EmptyStmt.class, "EmptyStmt", "com.github.javaparser.ast.stmt.EmptyStmt", "com.github.javaparser.ast.stmt", false);
    }

    private Field getField(String name) {
        try {
            return EmptyStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

