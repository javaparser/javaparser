package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationLevelMetaModel extends ClassMetaModel {

    ArrayCreationLevelMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ArrayCreationLevel.class, "ArrayCreationLevel", "com.github.javaparser.ast.ArrayCreationLevel", "com.github.javaparser.ast", false);
    }
}

