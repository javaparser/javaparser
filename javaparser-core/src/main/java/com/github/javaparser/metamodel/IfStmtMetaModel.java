package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.IfStmt;

public class IfStmtMetaModel extends ClassMetaModel {

    IfStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.IfStmt.class, "IfStmt", "com.github.javaparser.ast.stmt.IfStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField("condition"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getElseStmt", "setElseStmt", "elseStmt", com.github.javaparser.ast.stmt.Statement.class, getField("elseStmt"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThenStmt", "setThenStmt", "thenStmt", com.github.javaparser.ast.stmt.Statement.class, getField("thenStmt"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return IfStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

