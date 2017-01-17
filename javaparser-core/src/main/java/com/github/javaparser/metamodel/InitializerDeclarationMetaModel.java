package com.github.javaparser.metamodel;

import java.util.Optional;

public class InitializerDeclarationMetaModel extends ClassMetaModel {

    public InitializerDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

