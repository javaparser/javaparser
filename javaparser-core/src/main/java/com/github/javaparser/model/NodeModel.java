package com.github.javaparser.model;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.util.HashSet;
import java.util.Set;

public class NodeModel {
    private final JavaParserModel javaParserModel;
    private final Class<? extends Node> nodeClass;
    private final Set<FieldModel> fieldModels = new HashSet<>();
    private NodeModel superNodeModel;

    public NodeModel(JavaParserModel javaParserModel, Class<? extends Node> nodeClass) {
        this.javaParserModel = javaParserModel;
        this.nodeClass = nodeClass;
    }

    void initialize() {
        for (Field field : nodeClass.getDeclaredFields()) {
            fieldModels.add(new FieldModel(this, field));
        }

        Class<?> superclass = nodeClass.getSuperclass();
        if (Node.class.isAssignableFrom(superclass)) {
            superNodeModel = javaParserModel.getNodeModel(superclass).get();
        }

        fieldModels.forEach(FieldModel::initialize);
    }

    public NodeModel getSuperNodeModel() {
        return superNodeModel;
    }

    public JavaParserModel getJavaParserModel() {
        return javaParserModel;
    }

    public Set<FieldModel> getFieldModels() {
        return fieldModels;
    }

    public Class<? extends Node> getNodeClass() {
        return nodeClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        NodeModel nodeModel = (NodeModel) o;

        if (!nodeClass.equals(nodeModel.nodeClass)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return nodeClass.hashCode();
    }

    public String getClassName() {
        return nodeClass.getSimpleName();
    }
    public String getQualifiedClassName() {
        return nodeClass.getName();
    }
}
