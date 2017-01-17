package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceDeclarationMetaModel extends ClassMetaModel {

    public ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

