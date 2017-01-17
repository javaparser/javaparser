package com.github.javaparser.metamodel;

import com.github.javaparser.ast.NodeList;

import java.util.List;
import java.util.Optional;

/**
 * Meta-data about all classes in the AST.
 * These are all Nodes, except NodeList.
 */
public class ClassMetaModel {
    public final Optional<ClassMetaModel> superClassMetaModel;
    public final JavaParserMetaModel javaParserMetaModel;
    public final List<FieldMetaModel> fieldMetaModels;
    public final Class<?> reflectionClass;
    public final String className;
    public final String qualifiedClassName;
    public final String packageName;
    public final boolean isAbstract;
    public final Flags flags = new Flags();

    public ClassMetaModel(Optional<ClassMetaModel> superClassMetaModel, JavaParserMetaModel javaParserMetaModel, List<FieldMetaModel> fieldMetaModels, Class<?> reflectionClass, String className, String qualifiedClassName, String packageName, boolean isAbstract) {
        this.superClassMetaModel = superClassMetaModel;
        this.javaParserMetaModel = javaParserMetaModel;
        this.fieldMetaModels = fieldMetaModels;
        this.reflectionClass = reflectionClass;
        this.className = className;
        this.qualifiedClassName = qualifiedClassName;
        this.packageName = packageName;
        this.isAbstract = isAbstract;
    }

    public boolean is(Class<?> c) {
        return reflectionClass.equals(c);
    }
}
