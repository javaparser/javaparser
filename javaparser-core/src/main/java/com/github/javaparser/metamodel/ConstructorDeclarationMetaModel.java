package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConstructorDeclarationMetaModel extends ClassMetaModel {

    public ConstructorDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.ConstructorDeclaration.class, "ConstructorDeclaration", "com.github.javaparser.ast.body.ConstructorDeclaration", "com.github.javaparser.ast.body", false);
    }
}

