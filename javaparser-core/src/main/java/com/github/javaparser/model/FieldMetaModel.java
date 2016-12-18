package com.github.javaparser.model;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.capitalize;

/**
 * Meta-data about a field in a node in the AST.
 */
public class FieldMetaModel {
    private final ClassMetaModel classMetaModel;
    private final Field reflectionField;
    private String getterMethodName;
    private Flags flags = new Flags();
    private boolean optional;

    FieldMetaModel(ClassMetaModel classMetaModel, Field reflectionField) {
        this.classMetaModel = classMetaModel;
        this.reflectionField = reflectionField;
    }

    void initialize() {
        String name = reflectionField.getName();
        if (name.startsWith("is")) {
            getterMethodName = name;
        } else if (reflectionField.getType().equals(Boolean.class)) {
            getterMethodName = "is" + capitalize(name);
        } else {
            getterMethodName = "get" + capitalize(name);
        }

        try {
            Method method = classMetaModel.getReflectionClass().getMethod(getterMethodName);
            optional = method.getReturnType().equals(Optional.class);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FieldMetaModel that = (FieldMetaModel) o;

        if (!reflectionField.equals(that.reflectionField)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return reflectionField.hashCode();
    }

    public ClassMetaModel getClassMetaModel() {
        return classMetaModel;
    }

    public Field getReflectionField() {
        return reflectionField;
    }

    public String getter() {
        return getterMethodName + "()";
    }

    public String getName() {
        return reflectionField.getName();
    }

    public Class<?> getType() {
        return reflectionField.getType();
    }

    boolean isPartOfModel() {
        if (Modifier.isStatic(reflectionField.getModifiers()) ||
                is(Node.class, "parentNode") ||
                is("observers") ||
                is(NodeList.class, "innerList") ||
                is(Node.class, "data") ||
                is(Node.class, "range") ||
                is(Node.class, "childNodes")
                ) {
            return false;
        }
        return true;
    }

    public boolean is(Class<?> c, String fieldName) {
        return getClassMetaModel().is(c) && getName().equals(fieldName);
    }

    public boolean is(String fieldName) {
        return getName().equals(fieldName);
    }

    public Flags getFlags() {
        return flags;
    }

    public boolean isOptional() {
        return optional;
    }

    @Override
    public String toString() {
        return "(" + getType().getSimpleName() + ")\t" + classMetaModel.toString() + "#" + getName();
    }
}
