package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ReturnStmtMetaModel extends ClassMetaModel {

    ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ReturnStmt.class, "ReturnStmt", "com.github.javaparser.ast.stmt.ReturnStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ReturnStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

