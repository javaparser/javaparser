package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeParameterMetaModel extends ClassMetaModel {

    public TypeParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

