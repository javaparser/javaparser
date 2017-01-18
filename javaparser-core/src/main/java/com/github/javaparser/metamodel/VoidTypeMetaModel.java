package com.github.javaparser.metamodel;

import java.util.Optional;

public class VoidTypeMetaModel extends ClassMetaModel {

    VoidTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.VoidType.class, "VoidType", "com.github.javaparser.ast.type.VoidType", "com.github.javaparser.ast.type", false);
    }
}

