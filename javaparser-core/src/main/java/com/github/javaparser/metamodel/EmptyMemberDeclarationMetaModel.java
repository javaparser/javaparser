package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyMemberDeclarationMetaModel extends BodyDeclarationMetaModel {

    EmptyMemberDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.EmptyMemberDeclaration.class, "EmptyMemberDeclaration", "com.github.javaparser.ast.body", false, false);
    }
}
