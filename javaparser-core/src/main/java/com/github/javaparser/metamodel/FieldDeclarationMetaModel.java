package com.github.javaparser.metamodel;

import java.util.Optional;

public class FieldDeclarationMetaModel extends ClassMetaModel {

    FieldDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.FieldDeclaration.class, "FieldDeclaration", "com.github.javaparser.ast.body.FieldDeclaration", "com.github.javaparser.ast.body", false);
    }
}

