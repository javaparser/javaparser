package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReceiverParameterMetaModel extends NodeMetaModel {

    ReceiverParameterMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.ReceiverParameter.class, "ReceiverParameter", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}
