package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReferenceTypeMetaModel extends BaseNodeMetaModel {

    ReferenceTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.ReferenceType.class, "ReferenceType", "com.github.javaparser.ast.type", true);
    }
}

