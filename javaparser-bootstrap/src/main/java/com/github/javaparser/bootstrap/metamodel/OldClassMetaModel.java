package com.github.javaparser.bootstrap.metamodel;

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
public class OldClassMetaModel {
    private final OldJavaParserMetaModel oldJavaParserMetaModel;
    private final Class<?> reflectionClass;
    private final List<OldFieldMetaModel> oldFieldMetaModels = new ArrayList<>();
    private Optional<OldClassMetaModel> superClassMetaModel;
    private Flags flags = new Flags();
    
    OldClassMetaModel(OldJavaParserMetaModel oldJavaParserMetaModel, Class<?> reflectionClass) {
        this.oldJavaParserMetaModel = oldJavaParserMetaModel;
        this.reflectionClass = reflectionClass;
    }

    void initialize() {
        for (Field field : reflectionClass.getDeclaredFields()) {
            OldFieldMetaModel oldFieldMetaModel = new OldFieldMetaModel(this, field);
            if (oldFieldMetaModel.isPartOfModel()) {
                oldFieldMetaModels.add(oldFieldMetaModel);
            }
        }

        oldFieldMetaModels.sort(Comparator.comparing(OldFieldMetaModel::getName));

        Class<?> superclass = reflectionClass.getSuperclass();
        if (Node.class.isAssignableFrom(superclass)) {
            superClassMetaModel = oldJavaParserMetaModel.getClassMetaModel(superclass);
        } else {
            superClassMetaModel = Optional.empty();
        }

        oldFieldMetaModels.forEach(OldFieldMetaModel::initialize);
    }

    public Optional<OldClassMetaModel> getSuperClassMetaModel() {
        return superClassMetaModel;
    }

    public OldJavaParserMetaModel getOldJavaParserMetaModel() {
        return oldJavaParserMetaModel;
    }

    /**
     * Returns all fields, including fields of the super classes, as long as they are considered relevant to the AST.
     */
    public List<OldFieldMetaModel> getOldFieldMetaModels() {
        List<OldFieldMetaModel> allFields = new ArrayList<>();
        allFields.addAll(this.oldFieldMetaModels);
        superClassMetaModel.ifPresent(superClass -> allFields.addAll(superClass.getOldFieldMetaModels()));
        allFields.sort(Comparator.comparing(OldFieldMetaModel::getName));
        return allFields;
    }

    public Class<?> getReflectionClass() {
        return reflectionClass;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        OldClassMetaModel oldClassMetaModel = (OldClassMetaModel) o;

        if (!reflectionClass.equals(oldClassMetaModel.reflectionClass)) return false;

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
