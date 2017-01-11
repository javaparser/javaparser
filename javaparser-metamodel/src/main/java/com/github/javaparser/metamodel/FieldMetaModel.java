package com.github.javaparser.metamodel;

public class FieldMetaModel {
    public final ClassMetaModel classMetaModel;
    public final String getter;
    public final String setter;
    public final String name;
    public final String type;
    public final boolean isNode;
    public final boolean isOptional;
    public final boolean isList;
    public final boolean isSet;
    public final Flags flags = new Flags();

    public FieldMetaModel(ClassMetaModel classMetaModel, String getter, String setter, String name, String type, boolean isNode, boolean isOptional, boolean isList, boolean isSet) {
        this.classMetaModel = classMetaModel;
        this.getter = getter;
        this.setter = setter;
        this.name = name;
        this.type = type;
        this.isNode = isNode;
        this.isOptional = isOptional;
        this.isList = isList;
        this.isSet = isSet;
    }
}
