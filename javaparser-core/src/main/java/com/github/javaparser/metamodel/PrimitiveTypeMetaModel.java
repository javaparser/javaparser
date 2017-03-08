package com.github.javaparser.metamodel;

import java.util.Optional;

public class PrimitiveTypeMetaModel extends TypeMetaModel {

    PrimitiveTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.PrimitiveType.class, "PrimitiveType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel typePropertyMetaModel;
}
