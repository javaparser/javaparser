package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnionTypeMetaModel extends ClassMetaModel {

    public UnionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

