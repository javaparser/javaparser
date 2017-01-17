package com.github.javaparser.metamodel;

import java.util.Optional;

public class ObjectCreationExprMetaModel extends ClassMetaModel {

    public ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

