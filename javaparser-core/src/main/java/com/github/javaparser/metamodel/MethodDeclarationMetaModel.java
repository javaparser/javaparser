package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends ClassMetaModel {

    public MethodDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body.MethodDeclaration", "com.github.javaparser.ast.body", false);
    }
}

