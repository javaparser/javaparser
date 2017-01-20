package com.github.javaparser.metamodel;

import java.util.Optional;

public class PackageDeclarationMetaModel extends BaseNodeMetaModel {

    PackageDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.PackageDeclaration.class, "PackageDeclaration", "com.github.javaparser.ast.PackageDeclaration", "com.github.javaparser.ast", false);
    }
}

