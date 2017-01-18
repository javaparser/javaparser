package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.ArrayType;

public class ArrayTypeMetaModel extends ClassMetaModel {

    ArrayTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type.ArrayType", "com.github.javaparser.ast.type", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getComponentType", "setComponentType", "componentType", com.github.javaparser.ast.type.Type.class, getField("componentType"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ArrayType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

