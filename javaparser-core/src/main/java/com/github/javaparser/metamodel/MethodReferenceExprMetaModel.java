package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodReferenceExprMetaModel extends ClassMetaModel {

    public MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

