package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.StringLiteralExpr;

public class StringLiteralExprMetaModel extends ClassMetaModel {

    StringLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.StringLiteralExpr.class, "StringLiteralExpr", "com.github.javaparser.ast.expr.StringLiteralExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", java.lang.String.class, getField("value"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return StringLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

