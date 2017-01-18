package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;

public class ArrayInitializerExprMetaModel extends ClassMetaModel {

    ArrayInitializerExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayInitializerExpr.class, "ArrayInitializerExpr", "com.github.javaparser.ast.expr.ArrayInitializerExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getValues", "setValues", "values", com.github.javaparser.ast.expr.Expression.class, getField("values"), true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ArrayInitializerExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

