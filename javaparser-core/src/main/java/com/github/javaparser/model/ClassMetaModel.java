package com.github.javaparser.model;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * Meta-data about a type of node in the AST.
 * Exception: NodeList is in here, but is not a Node.
 */
public class ClassMetaModel {
    private final JavaParserMetaModel javaParserMetaModel;
    private final Class<?> reflectionClass;
    private final Set<FieldMetaModel> fieldMetaModels = new HashSet<>();
    private Optional<ClassMetaModel> superClassMetaModel;

    ClassMetaModel(JavaParserMetaModel javaParserMetaModel, Class<?> reflectionClass) {
        this.javaParserMetaModel = javaParserMetaModel;
        this.reflectionClass = reflectionClass;
    }

    void initialize() {
        for (Field field : reflectionClass.getDeclaredFields()) {
            FieldMetaModel fieldMetaModel = new FieldMetaModel(this, field);
            if (fieldMetaModel.isPartOfModel()) {
                fieldMetaModels.add(fieldMetaModel);
            }
        }

        Class<?> superclass = reflectionClass.getSuperclass();
        if (Node.class.isAssignableFrom(superclass)) {
            superClassMetaModel = javaParserMetaModel.getClassMetaModel(superclass);
        } else {
            superClassMetaModel = Optional.empty();
        }

        fieldMetaModels.forEach(FieldMetaModel::initialize);
    }

    public Optional<ClassMetaModel> getSuperClassMetaModel() {
        return superClassMetaModel;
    }

    public JavaParserMetaModel getJavaParserMetaModel() {
        return javaParserMetaModel;
    }

    /**
     * Returns all fields, including fields of the super classes, as long as they are considered relevant to the AST.
     */
    public Set<FieldMetaModel> getFieldMetaModels() {
        HashSet<FieldMetaModel> allFields = new HashSet<>();
        allFields.addAll(this.fieldMetaModels);
        superClassMetaModel.ifPresent(superClass -> allFields.addAll(superClass.getFieldMetaModels()));
        return allFields;
    }

    public Class<?> getReflectionClass() {
        return reflectionClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ClassMetaModel classMetaModel = (ClassMetaModel) o;

        if (!reflectionClass.equals(classMetaModel.reflectionClass)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return reflectionClass.hashCode();
    }

    public String getClassName() {
        return reflectionClass.getSimpleName();
    }

    public String getQualifiedClassName() {
        return reflectionClass.getName();
    }

    public boolean isAbstract() {
        return Modifier.isAbstract(reflectionClass.getModifiers());
    }
}
