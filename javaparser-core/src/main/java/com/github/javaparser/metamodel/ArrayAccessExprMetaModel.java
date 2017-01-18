package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ArrayAccessExprMetaModel extends ClassMetaModel {

    ArrayAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ArrayAccessExpr.class, "ArrayAccessExpr", "com.github.javaparser.ast.expr.ArrayAccessExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIndex", "setIndex", "index", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ArrayAccessExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

