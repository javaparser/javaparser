package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntersectionTypeMetaModel extends BaseNodeMetaModel {

    IntersectionTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.IntersectionType.class, "IntersectionType", "com.github.javaparser.ast.type.IntersectionType", "com.github.javaparser.ast.type", false);
    }
}

