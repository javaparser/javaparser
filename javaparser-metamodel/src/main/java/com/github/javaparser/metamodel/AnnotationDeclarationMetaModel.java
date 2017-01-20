package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationDeclarationMetaModel extends BaseNodeMetaModel {

    AnnotationDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.AnnotationDeclaration.class, "AnnotationDeclaration", "com.github.javaparser.ast.body.AnnotationDeclaration", "com.github.javaparser.ast.body", false);
    }
}

