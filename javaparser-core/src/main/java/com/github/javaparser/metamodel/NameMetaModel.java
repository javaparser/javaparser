package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends ClassMetaModel {

    public NameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

