package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.SynchronizedStmt;

public class SynchronizedStmtMetaModel extends ClassMetaModel {

    SynchronizedStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.SynchronizedStmt.class, "SynchronizedStmt", "com.github.javaparser.ast.stmt.SynchronizedStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.BlockStmt.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField("expression"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SynchronizedStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

