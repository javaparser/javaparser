package com.github.javaparser.model;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;

import static com.github.javaparser.utils.Utils.capitalize;

/**
 * Meta-data about a field in a node in the AST.
 */
public class FieldMetaModel {
    private final ClassMetaModel classMetaModel;
    private final Field reflectionField;
    private String getter;

    FieldMetaModel(ClassMetaModel classMetaModel, Field reflectionField) {
        this.classMetaModel = classMetaModel;
        this.reflectionField = reflectionField;
    }

    void initialize() {
        String name = reflectionField.getName();
        if (name.startsWith("is")) {
            getter = name + "()";
        } else if (reflectionField.getType().equals(Boolean.class)) {
            getter = "is" + capitalize(name) + "()";
        } else {
            getter = "get" + capitalize(name) + "()";
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
        return getter;
    }

    public String getName() {
        return reflectionField.getName();
    }

    public Class<?> getType() {
        return reflectionField.getType();
    }

    boolean isPartOfModel() {
        Class<?> type = getClassMetaModel().getReflectionClass();
        String name = getName();
        if (Modifier.isStatic(reflectionField.getModifiers())) {
            return false;
        }
        if (name.equals("observers")) {
            return false;
        }
        if (type.equals(NodeList.class)) {
            if (name.equals("innerList")) {
                return false;
            }
        }
        if (type.equals(Node.class)) {
            if (name.equals("data")) {
                return false;
            }
        }
        return true;
    }


}
