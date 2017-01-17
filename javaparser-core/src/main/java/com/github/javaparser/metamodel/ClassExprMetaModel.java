package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassExprMetaModel extends ClassMetaModel {

    public ClassExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

