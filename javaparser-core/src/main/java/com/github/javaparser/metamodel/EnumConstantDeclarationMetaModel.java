package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumConstantDeclarationMetaModel extends BodyDeclarationMetaModel {

    EnumConstantDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.EnumConstantDeclaration.class, "EnumConstantDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel argumentsPropertyMetaModel;

    public PropertyMetaModel classBodyPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
