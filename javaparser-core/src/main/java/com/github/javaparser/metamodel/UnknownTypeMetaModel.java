package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.type.UnknownType;

public class UnknownTypeMetaModel extends ClassMetaModel {

    UnknownTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.UnknownType.class, "UnknownType", "com.github.javaparser.ast.type.UnknownType", "com.github.javaparser.ast.type", false);
    }

    private Field getField(String name) {
        try {
            return UnknownType.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

