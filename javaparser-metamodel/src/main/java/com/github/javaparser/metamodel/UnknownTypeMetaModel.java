package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnknownTypeMetaModel extends BaseNodeMetaModel {

    UnknownTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.UnknownType.class, "UnknownType", "com.github.javaparser.ast.type", false, false);
    }
}

