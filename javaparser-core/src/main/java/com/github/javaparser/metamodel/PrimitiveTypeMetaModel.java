package com.github.javaparser.metamodel;

import java.util.Optional;

public class PrimitiveTypeMetaModel extends ClassMetaModel {

    public PrimitiveTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

