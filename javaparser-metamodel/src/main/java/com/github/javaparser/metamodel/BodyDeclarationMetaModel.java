package com.github.javaparser.metamodel;

import java.util.Optional;

public class BodyDeclarationMetaModel extends BaseNodeMetaModel {

    BodyDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.BodyDeclaration.class, "BodyDeclaration", "com.github.javaparser.ast.body.BodyDeclaration", "com.github.javaparser.ast.body", true);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;
}

