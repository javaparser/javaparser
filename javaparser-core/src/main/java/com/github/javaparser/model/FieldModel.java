package com.github.javaparser.model;

import java.lang.reflect.Field;

public class FieldModel {
    private final NodeModel nodeModel;
    private final Field field;

    public FieldModel(NodeModel nodeModel, Field field) {
        this.nodeModel = nodeModel;
        this.field = field;
    }
    
    void initialize() {
        
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FieldModel that = (FieldModel) o;

        if (!field.equals(that.field)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return field.hashCode();
    }

    public NodeModel getNodeModel() {
        return nodeModel;
    }

    public Field getField() {
        return field;
    }
}
