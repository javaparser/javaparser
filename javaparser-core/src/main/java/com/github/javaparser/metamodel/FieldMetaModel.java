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
    public final boolean isNodeList;
    public final boolean isSet;
    public final boolean hasWildcard;
    public final Flags flags = new Flags();

    public FieldMetaModel(ClassMetaModel classMetaModel, String getter, String setter, String name, Class<?> type, Field reflectionField, boolean isNode, boolean isOptional, boolean isNodeList, boolean isEnumSet, boolean hasWildcard) {
        this.classMetaModel = classMetaModel;
        this.getter = getter;
        this.setter = setter;
        this.name = name;
        this.type = type;
        this.reflectionField = reflectionField;
        this.isNode = isNode;
        this.isOptional = isOptional;
        this.isNodeList = isNodeList;
        this.isSet = isEnumSet;
        this.hasWildcard = hasWildcard;
    }

    public boolean is(Class<?> c, String fieldName) {
        return classMetaModel.is(c) && name.equals(fieldName);
    }

    public boolean is(String fieldName) {
        return name.equals(fieldName);
    }

//    public boolean is(Class<?> c, String fieldName) {
//        return getOldClassMetaModel().is(c) && getName().equals(fieldName);
//    }
//
//    public boolean is(String fieldName) {
//        return getName().equals(fieldName);
//    }

//    @Override
//    public String toString() {
//        return "(" + getType().getSimpleName() + ")\t" + oldClassMetaModel.toString() + "#" + getName();
//    }
//    @Override
//    public int hashCode() {
//        return reflectionField.hashCode();
//    }
//    @Override
//    public boolean equals(Object o) {
//        if (this == o) return true;
//        if (o == null || getClass() != o.getClass()) return false;
//
//        OldFieldMetaModel that = (OldFieldMetaModel) o;
//
//        if (!reflectionField.equals(that.reflectionField)) return false;
//
//        return true;
//    }
}
