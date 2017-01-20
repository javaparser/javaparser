package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumDeclarationMetaModel extends BaseNodeMetaModel {

    EnumDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumDeclaration.class, "EnumDeclaration", "com.github.javaparser.ast.body.EnumDeclaration", "com.github.javaparser.ast.body", false);
    }
}

