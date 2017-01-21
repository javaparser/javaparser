package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayTypeMetaModel extends BaseNodeMetaModel {

    ArrayTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type", false);
    }

    public PropertyMetaModel componentTypePropertyMetaModel;
}

