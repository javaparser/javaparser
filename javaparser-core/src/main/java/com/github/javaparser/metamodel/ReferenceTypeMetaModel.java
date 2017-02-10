package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReferenceTypeMetaModel extends BaseNodeMetaModel {

    ReferenceTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.ReferenceType.class, "ReferenceType", "com.github.javaparser.ast.type", true, true);
    }
}

