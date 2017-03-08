package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnionTypeMetaModel extends TypeMetaModel {

    UnionTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.UnionType.class, "UnionType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel elementsPropertyMetaModel;
}
