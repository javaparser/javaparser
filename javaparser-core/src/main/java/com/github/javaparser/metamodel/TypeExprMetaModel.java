package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class TypeExprMetaModel extends ClassMetaModel {

    TypeExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.TypeExpr.class, "TypeExpr", "com.github.javaparser.ast.expr.TypeExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

