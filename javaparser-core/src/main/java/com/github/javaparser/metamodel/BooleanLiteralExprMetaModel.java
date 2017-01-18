package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;

public class BooleanLiteralExprMetaModel extends ClassMetaModel {

    BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr.BooleanLiteralExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", boolean.class, getField("value"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return BooleanLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

