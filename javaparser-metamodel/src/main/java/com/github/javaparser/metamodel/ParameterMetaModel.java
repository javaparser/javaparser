package com.github.javaparser.metamodel;

import java.util.Optional;

public class ParameterMetaModel extends BaseNodeMetaModel {

    ParameterMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.Parameter.class, "Parameter", "com.github.javaparser.ast.body.Parameter", "com.github.javaparser.ast.body", false);
    }
}

