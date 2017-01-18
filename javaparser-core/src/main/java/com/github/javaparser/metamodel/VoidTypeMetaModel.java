package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.VoidType;

public class VoidTypeMetaModel extends ClassMetaModel {

    VoidTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.VoidType.class, "VoidType", "com.github.javaparser.ast.type.VoidType", "com.github.javaparser.ast.type", false);
    }

    private Field getField(String name) {
        try {
            return VoidType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

