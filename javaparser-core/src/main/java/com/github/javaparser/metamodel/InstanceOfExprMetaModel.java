package com.github.javaparser.metamodel;

import java.util.Optional;

public class InstanceOfExprMetaModel extends ClassMetaModel {

    public InstanceOfExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

