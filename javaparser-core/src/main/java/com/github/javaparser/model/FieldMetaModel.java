package com.github.javaparser.model;

import java.lang.reflect.Field;

public interface FieldMetaModel {
    ClassMetaModel getClassMetaModel();

    Field getReflectionField();

    String getter();

    String getName();

    Class<?> getType();

    Flags getFlags();

    boolean isOptional();

    boolean isList();

    boolean isSet();
}
