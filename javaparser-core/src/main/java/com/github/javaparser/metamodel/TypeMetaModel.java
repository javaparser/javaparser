package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeMetaModel extends ClassMetaModel {

    public TypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.Type.class, "Type", "com.github.javaparser.ast.type.Type", "com.github.javaparser.ast.type", true);
    }
}

