package com.github.javaparser.model;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Set;

/**
 * Meta-data about a type of node in the AST.
 * Exception: NodeList is in here, but is not a Node.
 */
public class NodeMetaModel {
    private final JavaParserMetaModel javaParserMetaModel;
    private final Class<?> nodeClass;
    private final Set<FieldMetaModel> fieldMetaModels = new HashSet<>();
    private NodeMetaModel superNodeMetaModel;

    public NodeMetaModel(JavaParserMetaModel javaParserMetaModel, Class<?> nodeClass) {
        this.javaParserMetaModel = javaParserMetaModel;
        this.nodeClass = nodeClass;
    }

    void initialize() {
        for (Field field : nodeClass.getDeclaredFields()) {
            fieldMetaModels.add(new FieldMetaModel(this, field));
        }

        Class<?> superclass = nodeClass.getSuperclass();
        if (Node.class.isAssignableFrom(superclass)) {
            superNodeMetaModel = javaParserMetaModel.getNodeModel(superclass).get();
        }

        fieldMetaModels.forEach(FieldMetaModel::initialize);
    }

    public NodeMetaModel getSuperNodeMetaModel() {
        return superNodeMetaModel;
    }

    public JavaParserMetaModel getJavaParserMetaModel() {
        return javaParserMetaModel;
    }

    public Set<FieldMetaModel> getFieldMetaModels() {
        return fieldMetaModels;
    }

    public Class<?> getNodeClass() {
        return nodeClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        NodeMetaModel nodeMetaModel = (NodeMetaModel) o;

        if (!nodeClass.equals(nodeMetaModel.nodeClass)) return false;

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

    public boolean isAbstract() {
        return Modifier.isAbstract(nodeClass.getModifiers());
    }
}
