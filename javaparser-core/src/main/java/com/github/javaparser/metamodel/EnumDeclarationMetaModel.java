package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumDeclarationMetaModel extends ClassMetaModel {

    EnumDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.EnumDeclaration.class, "EnumDeclaration", "com.github.javaparser.ast.body.EnumDeclaration", "com.github.javaparser.ast.body", false);
    }
}

