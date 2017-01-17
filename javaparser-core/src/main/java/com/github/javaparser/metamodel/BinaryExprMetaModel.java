package com.github.javaparser.metamodel;

import java.util.Optional;

public class BinaryExprMetaModel extends ClassMetaModel {

    public BinaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

