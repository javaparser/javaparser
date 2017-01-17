package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationMemberDeclarationMetaModel extends ClassMetaModel {

    public AnnotationMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

