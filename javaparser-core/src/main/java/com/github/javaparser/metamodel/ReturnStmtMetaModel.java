package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.ReturnStmt;

public class ReturnStmtMetaModel extends ClassMetaModel {

    ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ReturnStmt.class, "ReturnStmt", "com.github.javaparser.ast.stmt.ReturnStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField("expression"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ReturnStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

