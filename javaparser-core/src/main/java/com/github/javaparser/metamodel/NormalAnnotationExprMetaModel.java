package com.github.javaparser.metamodel;

import java.util.Optional;

public class NormalAnnotationExprMetaModel extends ClassMetaModel {

    public NormalAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

