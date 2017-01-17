package com.github.javaparser.metamodel;

import java.util.Optional;

public class FieldAccessExprMetaModel extends ClassMetaModel {

    public FieldAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

