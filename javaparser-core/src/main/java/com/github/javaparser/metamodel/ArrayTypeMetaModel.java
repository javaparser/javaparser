package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayTypeMetaModel extends ReferenceTypeMetaModel {

    ArrayTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel componentTypePropertyMetaModel;

    public PropertyMetaModel originPropertyMetaModel;
}
