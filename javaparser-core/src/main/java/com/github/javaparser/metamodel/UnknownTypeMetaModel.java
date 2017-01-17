package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnknownTypeMetaModel extends ClassMetaModel {

    public UnknownTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.UnknownType.class, "UnknownType", "com.github.javaparser.ast.type.UnknownType", "com.github.javaparser.ast.type", false);
    }
}

