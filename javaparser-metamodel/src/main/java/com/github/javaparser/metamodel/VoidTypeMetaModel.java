package com.github.javaparser.metamodel;

import java.util.Optional;

public class VoidTypeMetaModel extends BaseNodeMetaModel {

    VoidTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.VoidType.class, "VoidType", "com.github.javaparser.ast.type", false);
    }
}

