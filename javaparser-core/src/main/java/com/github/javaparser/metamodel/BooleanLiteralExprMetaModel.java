package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class BooleanLiteralExprMetaModel extends ClassMetaModel {

    BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr.BooleanLiteralExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", boolean.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return BooleanLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

