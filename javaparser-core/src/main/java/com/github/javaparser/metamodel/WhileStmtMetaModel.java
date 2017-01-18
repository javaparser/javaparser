package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.WhileStmt;

public class WhileStmtMetaModel extends ClassMetaModel {

    WhileStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.WhileStmt.class, "WhileStmt", "com.github.javaparser.ast.stmt.WhileStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField("condition"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return WhileStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

