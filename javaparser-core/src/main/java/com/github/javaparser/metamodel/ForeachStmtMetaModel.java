package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.stmt.ForeachStmt;

public class ForeachStmtMetaModel extends ClassMetaModel {

    ForeachStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ForeachStmt.class, "ForeachStmt", "com.github.javaparser.ast.stmt.ForeachStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getIterable", "setIterable", "iterable", com.github.javaparser.ast.expr.Expression.class, getField("iterable"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getVariable", "setVariable", "variable", com.github.javaparser.ast.expr.VariableDeclarationExpr.class, getField("variable"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ForeachStmt.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

