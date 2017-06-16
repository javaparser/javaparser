package com.github.javaparser.metamodel;

import java.util.Optional;

public class InitializerDeclarationMetaModel extends BodyDeclarationMetaModel {

    InitializerDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.InitializerDeclaration.class, "InitializerDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel isStaticPropertyMetaModel;
}
