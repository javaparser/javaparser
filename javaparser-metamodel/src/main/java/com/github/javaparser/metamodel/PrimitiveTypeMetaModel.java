package com.github.javaparser.metamodel;

import java.util.Optional;

public class PrimitiveTypeMetaModel extends ClassMetaModel {

    PrimitiveTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.PrimitiveType.class, "PrimitiveType", "com.github.javaparser.ast.type.PrimitiveType", "com.github.javaparser.ast.type", false);
    }
}

