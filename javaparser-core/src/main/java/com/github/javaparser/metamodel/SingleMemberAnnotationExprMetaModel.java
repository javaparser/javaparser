package com.github.javaparser.metamodel;

import java.util.Optional;

public class SingleMemberAnnotationExprMetaModel extends ClassMetaModel {

    public SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

