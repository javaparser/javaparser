package com.github.javaparser.metamodel;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Meta-data about all classes in the AST.
 * These are all Nodes, except NodeList.
 */
public class BaseNodeMetaModel {
    public final Optional<BaseNodeMetaModel> superClassMetaModel;
    public final JavaParserMetaModel javaParserMetaModel;
    public final List<PropertyMetaModel> propertyMetaModels = new ArrayList<>();
    public final Class<?> reflectionClass;
    public final String name;
    public final String qualifiedClassName;
    public final String packageName;
    public final boolean isAbstract;

    public BaseNodeMetaModel(Optional<BaseNodeMetaModel> superClassMetaModel, JavaParserMetaModel javaParserMetaModel, Class<?> reflectionClass, String name, String qualifiedClassName, String packageName, boolean isAbstract) {
        this.superClassMetaModel = superClassMetaModel;
        this.javaParserMetaModel = javaParserMetaModel;
        this.reflectionClass = reflectionClass;
        this.name = name;
        this.qualifiedClassName = qualifiedClassName;
        this.packageName = packageName;
        this.isAbstract = isAbstract;
    }

    public boolean is(Class<?> c) {
        return reflectionClass.equals(c);
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
