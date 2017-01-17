package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationDeclarationMetaModel extends ClassMetaModel {

    public AnnotationDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.AnnotationDeclaration.class, "AnnotationDeclaration", "com.github.javaparser.ast.body.AnnotationDeclaration", "com.github.javaparser.ast.body", false);
    }
}

