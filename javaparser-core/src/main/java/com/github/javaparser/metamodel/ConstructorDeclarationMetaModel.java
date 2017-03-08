package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConstructorDeclarationMetaModel extends CallableDeclarationMetaModel {

    ConstructorDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.ConstructorDeclaration.class, "ConstructorDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;
}
