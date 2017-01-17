package com.github.javaparser.metamodel;

import java.util.Optional;

public class SuperExprMetaModel extends ClassMetaModel {

    public SuperExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

