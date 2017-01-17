package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnclosedExprMetaModel extends ClassMetaModel {

    public EnclosedExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

