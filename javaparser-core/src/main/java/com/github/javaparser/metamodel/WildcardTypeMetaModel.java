package com.github.javaparser.metamodel;

import java.util.Optional;

public class WildcardTypeMetaModel extends ClassMetaModel {

    public WildcardTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

