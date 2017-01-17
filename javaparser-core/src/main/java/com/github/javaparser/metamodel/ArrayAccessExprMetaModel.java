package com.github.javaparser.metamodel;

import java.util.Optional;

public class ArrayAccessExprMetaModel extends ClassMetaModel {

    public ArrayAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

