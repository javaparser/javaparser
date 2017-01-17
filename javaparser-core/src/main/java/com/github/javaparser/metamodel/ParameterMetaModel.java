package com.github.javaparser.metamodel;

import java.util.Optional;

public class ParameterMetaModel extends ClassMetaModel {

    public ParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

