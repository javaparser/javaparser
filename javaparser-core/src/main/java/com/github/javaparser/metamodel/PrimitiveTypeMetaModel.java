package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class PrimitiveTypeMetaModel extends ClassMetaModel {

    PrimitiveTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.PrimitiveType.class, "PrimitiveType", "com.github.javaparser.ast.type.PrimitiveType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.PrimitiveType.Primitive.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return PrimitiveTypeMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

