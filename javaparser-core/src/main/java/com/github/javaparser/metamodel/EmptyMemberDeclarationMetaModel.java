package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyMemberDeclarationMetaModel extends ClassMetaModel {

    public EmptyMemberDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

