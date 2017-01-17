package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntersectionTypeMetaModel extends ClassMetaModel {

    public IntersectionTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

