package com.github.javaparser.metamodel;

import java.util.Optional;

public class WildcardTypeMetaModel extends BaseNodeMetaModel {

    WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type.WildcardType", "com.github.javaparser.ast.type", false);
    }
}

