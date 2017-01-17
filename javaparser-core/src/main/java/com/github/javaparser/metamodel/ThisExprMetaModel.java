package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThisExprMetaModel extends ClassMetaModel {

    public ThisExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

