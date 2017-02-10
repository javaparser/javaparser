package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeDeclarationMetaModel extends BaseNodeMetaModel {

    TypeDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.TypeDeclaration.class, "TypeDeclaration", "com.github.javaparser.ast.body", true, true);
    }

    public PropertyMetaModel membersPropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}

