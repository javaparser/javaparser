package com.github.javaparser.metamodel;

import java.util.Optional;

public class LiteralExprMetaModel extends ClassMetaModel {

    public LiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

