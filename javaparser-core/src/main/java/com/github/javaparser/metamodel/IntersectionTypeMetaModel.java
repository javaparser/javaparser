package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntersectionTypeMetaModel extends TypeMetaModel {

    IntersectionTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.IntersectionType.class, "IntersectionType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel elementsPropertyMetaModel;
}
