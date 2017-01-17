package com.github.javaparser.metamodel;

import java.util.Optional;

public class InitializerDeclarationMetaModel extends ClassMetaModel {

    public InitializerDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.InitializerDeclaration.class, "InitializerDeclaration", "com.github.javaparser.ast.body.InitializerDeclaration", "com.github.javaparser.ast.body", false);
    }
}

