package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.EmptyStmt;

public class EmptyStmtMetaModel extends ClassMetaModel {

    EmptyStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.EmptyStmt.class, "EmptyStmt", "com.github.javaparser.ast.stmt.EmptyStmt", "com.github.javaparser.ast.stmt", false);
    }

    private Field getField(String name) {
        try {
            return EmptyStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

