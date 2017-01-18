package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ExpressionStmtMetaModel extends ClassMetaModel {

    ExpressionStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ExpressionStmt.class, "ExpressionStmt", "com.github.javaparser.ast.stmt.ExpressionStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ExpressionStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

