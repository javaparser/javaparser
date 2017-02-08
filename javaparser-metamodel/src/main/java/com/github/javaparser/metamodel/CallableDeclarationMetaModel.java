package com.github.javaparser.metamodel;

import java.util.Optional;

public class CallableDeclarationMetaModel extends BaseNodeMetaModel {

    CallableDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.CallableDeclaration.class, "CallableDeclaration", "com.github.javaparser.ast.body", true, true);
    }

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel parametersPropertyMetaModel;

    public PropertyMetaModel thrownExceptionsPropertyMetaModel;

    public PropertyMetaModel typeParametersPropertyMetaModel;
}

