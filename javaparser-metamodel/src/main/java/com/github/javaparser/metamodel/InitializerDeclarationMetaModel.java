package com.github.javaparser.metamodel;

import java.util.Optional;

public class InitializerDeclarationMetaModel extends ClassMetaModel {

    InitializerDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.InitializerDeclaration.class, "InitializerDeclaration", "com.github.javaparser.ast.body.InitializerDeclaration", "com.github.javaparser.ast.body", false);
    }
}

