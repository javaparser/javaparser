package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnknownTypeMetaModel extends TypeMetaModel {

    UnknownTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.UnknownType.class, "UnknownType", "com.github.javaparser.ast.type", false, false);
    }
}
