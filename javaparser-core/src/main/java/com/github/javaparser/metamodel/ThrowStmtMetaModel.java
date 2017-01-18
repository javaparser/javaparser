package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ThrowStmtMetaModel extends ClassMetaModel {

    ThrowStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ThrowStmt.class, "ThrowStmt", "com.github.javaparser.ast.stmt.ThrowStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ThrowStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

