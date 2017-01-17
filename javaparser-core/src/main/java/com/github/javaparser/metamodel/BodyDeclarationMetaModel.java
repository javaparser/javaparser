package com.github.javaparser.metamodel;

import java.util.Optional;

public class BodyDeclarationMetaModel extends ClassMetaModel {

    public BodyDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.BodyDeclaration.class, "BodyDeclaration", "com.github.javaparser.ast.body.BodyDeclaration", "com.github.javaparser.ast.body", true);
    }
}

