package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ForeachStmtMetaModel extends ClassMetaModel {

    ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt.ForeachStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIterable", "setIterable", "iterable", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariable", "setVariable", "variable", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ForeachStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

