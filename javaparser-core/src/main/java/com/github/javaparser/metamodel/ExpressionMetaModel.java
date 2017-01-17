package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionMetaModel extends ClassMetaModel {

    public ExpressionMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

