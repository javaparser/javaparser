package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReferenceTypeMetaModel extends ClassMetaModel {

    public ReferenceTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

