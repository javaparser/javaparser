package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends BaseNodeMetaModel {

    MethodDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel isDefaultPropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel parametersPropertyMetaModel;

    public PropertyMetaModel thrownExceptionsPropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;

    public PropertyMetaModel typeParametersPropertyMetaModel;
}

