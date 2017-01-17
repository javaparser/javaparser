package com.github.javaparser.metamodel;

import java.util.Optional;

public class BodyDeclarationMetaModel extends ClassMetaModel {

    public BodyDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

