package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnknownTypeMetaModel extends ClassMetaModel {

    UnknownTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.UnknownType.class, "UnknownType", "com.github.javaparser.ast.type.UnknownType", "com.github.javaparser.ast.type", false);
    }
}

