package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodCallExprMetaModel extends ClassMetaModel {

    public MethodCallExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

