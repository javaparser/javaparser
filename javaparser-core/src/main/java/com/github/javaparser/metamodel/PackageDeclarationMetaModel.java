package com.github.javaparser.metamodel;

import java.util.Optional;

public class PackageDeclarationMetaModel extends ClassMetaModel {

    public PackageDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

