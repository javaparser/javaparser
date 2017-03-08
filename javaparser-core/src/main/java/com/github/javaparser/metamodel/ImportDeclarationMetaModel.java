package com.github.javaparser.metamodel;

import java.util.Optional;

public class ImportDeclarationMetaModel extends NodeMetaModel {

    ImportDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.ImportDeclaration.class, "ImportDeclaration", "com.github.javaparser.ast", false, false);
    }

    public PropertyMetaModel isAsteriskPropertyMetaModel;

    public PropertyMetaModel isStaticPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;
}
