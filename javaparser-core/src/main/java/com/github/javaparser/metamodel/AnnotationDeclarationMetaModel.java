package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationDeclarationMetaModel extends TypeDeclarationMetaModel {

    AnnotationDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.AnnotationDeclaration.class, "AnnotationDeclaration", "com.github.javaparser.ast.body", false, false);
    }
}
