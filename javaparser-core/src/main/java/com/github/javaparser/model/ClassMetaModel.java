package com.github.javaparser.model;

import com.github.javaparser.ast.Node;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

/**
 * Meta-data about all classes in the AST.
 * These are all Nodes, except NodeList.
 */
public class ClassMetaModel {
    private final JavaParserMetaModel javaParserMetaModel;
    private final Class<?> reflectionClass;
    private final List<FieldMetaModel> fieldMetaModels = new ArrayList<>();
    private Optional<ClassMetaModel> superClassMetaModel;
    private Flags flags = new Flags();
    
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

        fieldMetaModels.sort(Comparator.comparing(FieldMetaModel::getName));

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
    public List<FieldMetaModel> getFieldMetaModels() {
        List<FieldMetaModel> allFields = new ArrayList<>();
        allFields.addAll(this.fieldMetaModels);
        superClassMetaModel.ifPresent(superClass -> allFields.addAll(superClass.getFieldMetaModels()));
        allFields.sort(Comparator.comparing(FieldMetaModel::getName));
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

    public boolean is(Class<?> c) {
        return reflectionClass.equals(c);
    }

    public Flags getFlags() {
        return flags;
    }

    @Override
    public String toString() {
        return getClassName();
    }
}
