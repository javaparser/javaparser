package com.github.javaparser.metamodel;

import java.lang.reflect.Field;

/**
 * Meta-data about a field in a node in the AST.
 */
public class FieldMetaModel {
    public final ClassMetaModel classMetaModel;
    public final String getter;
    public final String setter;
    public final String name;
    public final Class<?> type;
    public final Field reflectionField;
    public final boolean isNode;
    public final boolean isOptional;
    public final boolean isList;
    public final boolean isSet;
    public final Flags flags = new Flags();

    public FieldMetaModel(ClassMetaModel classMetaModel, String getter, String setter, String name, Class<?> type, Field reflectionField, boolean isNode, boolean isOptional, boolean isList, boolean isSet) {
        this.classMetaModel = classMetaModel;
        this.getter = getter;
        this.setter = setter;
        this.name = name;
        this.type = type;
        this.reflectionField = reflectionField;
        this.isNode = isNode;
        this.isOptional = isOptional;
        this.isList = isList;
        this.isSet = isSet;
    }

    public boolean is(Class<?> c, String fieldName) {
        return classMetaModel.is(c) && name.equals(fieldName);
    }

    public boolean is(String fieldName) {
        return name.equals(fieldName);
    }

}
