package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyMemberDeclarationMetaModel extends BaseNodeMetaModel {

    EmptyMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.EmptyMemberDeclaration.class, "EmptyMemberDeclaration", "com.github.javaparser.ast.body", false);
    }
}

