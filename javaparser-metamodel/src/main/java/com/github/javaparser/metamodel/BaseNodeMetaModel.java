package com.github.javaparser.metamodel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Meta-data about all classes in the AST.
 * These are all Nodes, except NodeList.
 */
public class BaseNodeMetaModel {
    private final Optional<BaseNodeMetaModel> superNodeMetaModel;
    private final JavaParserMetaModel javaParserMetaModel;
    private final List<PropertyMetaModel> propertyMetaModels = new ArrayList<>();
    private final Class<?> reflectionClass;
    private final String name;
    private final String packageName;
    private final boolean isAbstract;

    public BaseNodeMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, JavaParserMetaModel javaParserMetaModel, Class<?> reflectionClass, String name, String packageName, boolean isAbstract) {
        this.superNodeMetaModel = superNodeMetaModel;
        this.javaParserMetaModel = javaParserMetaModel;
        this.reflectionClass = reflectionClass;
        this.name = name;
        this.packageName = packageName;
        this.isAbstract = isAbstract;
    }

    public boolean is(Class<?> c) {
        return reflectionClass.equals(c);
    }

    public String getQualifiedClassName() {
        return packageName + "." + name;
    }

    public Optional<BaseNodeMetaModel> getSuperNodeMetaModel() {
        return superNodeMetaModel;
    }

    public JavaParserMetaModel getJavaParserMetaModel() {
        return javaParserMetaModel;
    }

    public List<PropertyMetaModel> getPropertyMetaModels() {
        return propertyMetaModels;
    }

    public Class<?> getReflectionClass() {
        return reflectionClass;
    }

    public String getName() {
        return name;
    }

    public String getPackageName() {
        return packageName;
    }

    public boolean isAbstract() {
        return isAbstract;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BaseNodeMetaModel classMetaModel = (BaseNodeMetaModel) o;

        if (!reflectionClass.equals(classMetaModel.reflectionClass)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return reflectionClass.hashCode();
    }

    @Override
    public String toString() {
        return name;
    }
}
