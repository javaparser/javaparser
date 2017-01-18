package com.github.javaparser.metamodel;

import java.util.Optional;

public class PackageDeclarationMetaModel extends ClassMetaModel {

    PackageDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.PackageDeclaration.class, "PackageDeclaration", "com.github.javaparser.ast.PackageDeclaration", "com.github.javaparser.ast", false);
    }
}

