package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class AssertStmtMetaModel extends ClassMetaModel {

    AssertStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.AssertStmt.class, "AssertStmt", "com.github.javaparser.ast.stmt.AssertStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCheck", "setCheck", "check", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getMessage", "setMessage", "message", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return AssertStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

