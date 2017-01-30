package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumDeclarationMetaModel extends BaseNodeMetaModel {

    EnumDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.EnumDeclaration.class, "EnumDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel entriesPropertyMetaModel;

    public PropertyMetaModel implementedTypesPropertyMetaModel;
}

