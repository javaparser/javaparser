package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.LambdaExpr;

public class LambdaExprMetaModel extends ClassMetaModel {

    LambdaExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LambdaExpr.class, "LambdaExpr", "com.github.javaparser.ast.expr.LambdaExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getBody", "setBody", "body", com.github.javaparser.ast.stmt.Statement.class, getField("body"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isEnclosingParameters", "setIsEnclosingParameters", "isEnclosingParameters", boolean.class, getField("isEnclosingParameters"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getParameters", "setParameters", "parameters", com.github.javaparser.ast.body.Parameter.class, getField("parameters"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return LambdaExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

