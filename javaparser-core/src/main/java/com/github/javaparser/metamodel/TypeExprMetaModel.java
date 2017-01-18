package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.TypeExpr;

public class TypeExprMetaModel extends ClassMetaModel {

    TypeExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.TypeExpr.class, "TypeExpr", "com.github.javaparser.ast.expr.TypeExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.Type.class, getField("type"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

