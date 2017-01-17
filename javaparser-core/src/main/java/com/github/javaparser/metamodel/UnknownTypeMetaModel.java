package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnknownTypeMetaModel extends ClassMetaModel {

    public UnknownTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

