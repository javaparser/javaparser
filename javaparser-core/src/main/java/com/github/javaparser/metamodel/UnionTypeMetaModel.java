package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnionTypeMetaModel extends ClassMetaModel {

    public UnionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.UnionType.class, "UnionType", "com.github.javaparser.ast.type.UnionType", "com.github.javaparser.ast.type", false);
    }
}

