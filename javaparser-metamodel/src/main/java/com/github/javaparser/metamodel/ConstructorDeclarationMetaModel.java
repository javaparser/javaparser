package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConstructorDeclarationMetaModel extends BaseNodeMetaModel {

    ConstructorDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.ConstructorDeclaration.class, "ConstructorDeclaration", "com.github.javaparser.ast.body.ConstructorDeclaration", "com.github.javaparser.ast.body", false);
    }
}

