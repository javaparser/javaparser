package com.github.javaparser.metamodel;

import java.util.Optional;

public class NullLiteralExprMetaModel extends ClassMetaModel {

    public NullLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

