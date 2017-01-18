package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class TypeMetaModel extends ClassMetaModel {

    TypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.Type.class, "Type", "com.github.javaparser.ast.type.Type", "com.github.javaparser.ast.type", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnnotations", "setAnnotations", "annotations", com.github.javaparser.ast.expr.AnnotationExpr.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return TypeMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

