package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumDeclarationMetaModel extends ClassMetaModel {

    public EnumDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

