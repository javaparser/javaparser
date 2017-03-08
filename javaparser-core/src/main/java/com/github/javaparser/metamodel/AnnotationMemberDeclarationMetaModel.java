package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationMemberDeclarationMetaModel extends BodyDeclarationMetaModel {

    AnnotationMemberDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.AnnotationMemberDeclaration.class, "AnnotationMemberDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel defaultValuePropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;
}
