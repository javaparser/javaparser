package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends ClassMetaModel {

    public MethodDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

