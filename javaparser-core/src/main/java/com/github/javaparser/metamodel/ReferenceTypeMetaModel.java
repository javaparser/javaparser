package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReferenceTypeMetaModel extends ClassMetaModel {

    public ReferenceTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.ReferenceType.class, "ReferenceType", "com.github.javaparser.ast.type.ReferenceType", "com.github.javaparser.ast.type", true);
    }
}

