package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class EnclosedExprMetaModel extends ClassMetaModel {

    EnclosedExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.EnclosedExpr.class, "EnclosedExpr", "com.github.javaparser.ast.expr.EnclosedExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getInner", "setInner", "inner", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
    }

    private Field getField(String name) {
        try {
            return EnclosedExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

