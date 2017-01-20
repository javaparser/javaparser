package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumConstantDeclarationMetaModel extends BaseNodeMetaModel {

    EnumConstantDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumConstantDeclaration.class, "EnumConstantDeclaration", "com.github.javaparser.ast.body.EnumConstantDeclaration", "com.github.javaparser.ast.body", false);
    }
}

