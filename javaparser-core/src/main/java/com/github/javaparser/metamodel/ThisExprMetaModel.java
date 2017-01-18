package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.ThisExpr;

public class ThisExprMetaModel extends ClassMetaModel {

    ThisExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ThisExpr.class, "ThisExpr", "com.github.javaparser.ast.expr.ThisExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getClassExpr", "setClassExpr", "classExpr", com.github.javaparser.ast.expr.Expression.class, getField("classExpr"), true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ThisExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

