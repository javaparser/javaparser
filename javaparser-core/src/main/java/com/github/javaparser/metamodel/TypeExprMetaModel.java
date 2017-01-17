package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeExprMetaModel extends ClassMetaModel {

    public TypeExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

