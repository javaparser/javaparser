package com.github.javaparser.metamodel;

import java.util.Optional;

public class VoidTypeMetaModel extends ClassMetaModel {

    public VoidTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

