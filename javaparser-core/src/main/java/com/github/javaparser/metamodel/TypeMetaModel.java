package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeMetaModel extends BaseNodeMetaModel {

    TypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.Type.class, "Type", "com.github.javaparser.ast.type", true, false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;
}

