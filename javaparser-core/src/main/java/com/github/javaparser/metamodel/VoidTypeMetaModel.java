package com.github.javaparser.metamodel;

import java.util.Optional;

public class VoidTypeMetaModel extends BaseNodeMetaModel {

    VoidTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.VoidType.class, "VoidType", "com.github.javaparser.ast.type", false, false);
    }
}

