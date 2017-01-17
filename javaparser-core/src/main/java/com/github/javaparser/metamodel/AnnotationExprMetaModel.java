package com.github.javaparser.metamodel;

import java.util.Optional;

public class AnnotationExprMetaModel extends ClassMetaModel {

    public AnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

