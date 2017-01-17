package com.github.javaparser.metamodel;

import java.util.Optional;

public class WildcardTypeMetaModel extends ClassMetaModel {

    public WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type.WildcardType", "com.github.javaparser.ast.type", false);
    }
}

