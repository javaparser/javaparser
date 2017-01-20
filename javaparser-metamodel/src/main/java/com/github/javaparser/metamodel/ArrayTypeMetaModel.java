package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayTypeMetaModel extends BaseNodeMetaModel {

    ArrayTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.ArrayType.class, "ArrayType", "com.github.javaparser.ast.type.ArrayType", "com.github.javaparser.ast.type", false);
    }
}

