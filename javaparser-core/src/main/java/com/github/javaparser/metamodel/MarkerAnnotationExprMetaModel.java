package com.github.javaparser.metamodel;

import java.util.Optional;

public class MarkerAnnotationExprMetaModel extends ClassMetaModel {

    public MarkerAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

