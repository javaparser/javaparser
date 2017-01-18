package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.SuperExpr;

public class SuperExprMetaModel extends ClassMetaModel {

    SuperExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SuperExpr.class, "SuperExpr", "com.github.javaparser.ast.expr.SuperExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField("classExpr"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SuperExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

