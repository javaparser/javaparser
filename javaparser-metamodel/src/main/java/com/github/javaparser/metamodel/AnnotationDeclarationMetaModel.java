package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationDeclarationMetaModel extends ClassMetaModel {

    AnnotationDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.AnnotationDeclaration.class, "AnnotationDeclaration", "com.github.javaparser.ast.body.AnnotationDeclaration", "com.github.javaparser.ast.body", false);
    }
}

