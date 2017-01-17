package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationMemberDeclarationMetaModel extends ClassMetaModel {

    public AnnotationMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.AnnotationMemberDeclaration.class, "AnnotationMemberDeclaration", "com.github.javaparser.ast.body.AnnotationMemberDeclaration", "com.github.javaparser.ast.body", false);
    }
}

