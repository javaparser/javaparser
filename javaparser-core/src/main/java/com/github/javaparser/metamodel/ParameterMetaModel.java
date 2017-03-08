package com.github.javaparser.metamodel;

import java.util.Optional;

public class ParameterMetaModel extends NodeMetaModel {

    ParameterMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.Parameter.class, "Parameter", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;

    public PropertyMetaModel isVarArgsPropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;

    public PropertyMetaModel varArgsAnnotationsPropertyMetaModel;
}
