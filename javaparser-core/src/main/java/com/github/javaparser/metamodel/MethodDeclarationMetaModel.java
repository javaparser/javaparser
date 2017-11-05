package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends CallableDeclarationMetaModel {

    MethodDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}
