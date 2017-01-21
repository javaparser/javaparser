package com.github.javaparser.metamodel;

import java.lang.reflect.Field;

import static com.github.javaparser.utils.Utils.capitalize;

/**
 * Meta-data about a property of a node in the AST.
 */
public class PropertyMetaModel {
    public final BaseNodeMetaModel classMetaModel;
    public final String name;
    public final Class<?> type;
    //    public Optional<CommentMetaModel> typeReference;
//    public Optional<Class<Integer>> tpe;
    public final Field reflectionField;
    public final boolean isNode;
    public final boolean isOptional;
    public final boolean isNodeList;
    public final boolean isSet;
    public final boolean hasWildcard;

    public PropertyMetaModel(BaseNodeMetaModel classMetaModel, String name, Class<?> type, Field reflectionField, boolean isNode, boolean isOptional, boolean isNodeList, boolean isEnumSet, boolean hasWildcard) {
        this.classMetaModel = classMetaModel;
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

    public String getSetterMethodName() {
        return "set" + capitalize(reflectionField.getName());
    }

    public String getGetterMethodName() {
        String name = reflectionField.getName();
        if (name.startsWith("is")) {
            return name;
        } else if (reflectionField.getType().equals(Boolean.class)) {
            return "is" + capitalize(name);
        }
        return "get" + capitalize(name);
    }

    @Override
    public String toString() {
        return "(" + type.getSimpleName() + ")\t" + classMetaModel + "#" + name;
    }

    @Override
    public int hashCode() {
        return reflectionField.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PropertyMetaModel that = (PropertyMetaModel) o;

        if (!reflectionField.equals(that.reflectionField)) return false;

        return true;
    }
}
