package com.github.javaparser.metamodel;

import java.util.Optional;

public class LambdaExprMetaModel extends ClassMetaModel {

    public LambdaExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

