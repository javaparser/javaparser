package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayCreationLevelMetaModel extends BaseNodeMetaModel {

    ArrayCreationLevelMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.ArrayCreationLevel.class, "ArrayCreationLevel", "com.github.javaparser.ast.ArrayCreationLevel", "com.github.javaparser.ast", false);
    }
}

