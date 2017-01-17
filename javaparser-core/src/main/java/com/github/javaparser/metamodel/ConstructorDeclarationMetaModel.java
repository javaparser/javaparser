package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConstructorDeclarationMetaModel extends ClassMetaModel {

    public ConstructorDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

