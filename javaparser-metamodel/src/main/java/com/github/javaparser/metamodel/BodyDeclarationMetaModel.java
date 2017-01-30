package com.github.javaparser.metamodel;

import java.util.Optional;

public class BodyDeclarationMetaModel extends BaseNodeMetaModel {

    BodyDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.BodyDeclaration.class, "BodyDeclaration", "com.github.javaparser.ast.body", true, true);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;
}

