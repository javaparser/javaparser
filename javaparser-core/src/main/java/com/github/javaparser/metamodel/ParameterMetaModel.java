package com.github.javaparser.metamodel;

import java.util.Optional;

public class ParameterMetaModel extends ClassMetaModel {

    public ParameterMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.Parameter.class, "Parameter", "com.github.javaparser.ast.body.Parameter", "com.github.javaparser.ast.body", false);
    }
}

