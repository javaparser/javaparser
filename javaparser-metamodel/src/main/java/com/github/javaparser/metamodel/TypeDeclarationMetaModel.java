package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeDeclarationMetaModel extends BaseNodeMetaModel {

    TypeDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.TypeDeclaration.class, "TypeDeclaration", "com.github.javaparser.ast.body.TypeDeclaration", "com.github.javaparser.ast.body", true);
    }
}

