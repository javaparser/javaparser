package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.PrimitiveType;

public class PrimitiveTypeMetaModel extends ClassMetaModel {

    PrimitiveTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.PrimitiveType.class, "PrimitiveType", "com.github.javaparser.ast.type.PrimitiveType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.PrimitiveType.Primitive.class, getField("type"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return PrimitiveType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

