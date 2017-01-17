package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends ClassMetaModel {

    public UnaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

