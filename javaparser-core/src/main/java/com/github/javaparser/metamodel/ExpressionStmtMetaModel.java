package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.ExpressionStmt;

public class ExpressionStmtMetaModel extends ClassMetaModel {

    ExpressionStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ExpressionStmt.class, "ExpressionStmt", "com.github.javaparser.ast.stmt.ExpressionStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField("expression"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ExpressionStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

