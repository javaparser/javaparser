package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeDeclarationMetaModel extends ClassMetaModel {

    public TypeDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.TypeDeclaration.class, "TypeDeclaration", "com.github.javaparser.ast.body.TypeDeclaration", "com.github.javaparser.ast.body", true);
    }
}

