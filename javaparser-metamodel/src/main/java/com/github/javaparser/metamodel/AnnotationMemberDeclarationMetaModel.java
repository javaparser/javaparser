package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationMemberDeclarationMetaModel extends BaseNodeMetaModel {

    AnnotationMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.AnnotationMemberDeclaration.class, "AnnotationMemberDeclaration", "com.github.javaparser.ast.body.AnnotationMemberDeclaration", "com.github.javaparser.ast.body", false);
    }
}

