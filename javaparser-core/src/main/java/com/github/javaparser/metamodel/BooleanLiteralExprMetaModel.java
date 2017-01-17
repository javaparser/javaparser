package com.github.javaparser.metamodel;

import java.util.Optional;

public class BooleanLiteralExprMetaModel extends ClassMetaModel {

    public BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

