package com.github.javaparser.metamodel;

import java.util.Optional;

public class PackageDeclarationMetaModel extends ClassMetaModel {

    public PackageDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.PackageDeclaration.class, "PackageDeclaration", "com.github.javaparser.ast.PackageDeclaration", "com.github.javaparser.ast", false);
    }
}

