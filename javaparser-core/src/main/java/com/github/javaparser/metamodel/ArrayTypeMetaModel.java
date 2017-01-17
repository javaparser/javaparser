package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayTypeMetaModel extends ClassMetaModel {

    public ArrayTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type.ArrayType", "com.github.javaparser.ast.type", false);
    }
}

