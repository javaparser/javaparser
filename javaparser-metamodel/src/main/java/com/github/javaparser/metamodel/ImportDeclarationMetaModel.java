package com.github.javaparser.metamodel;

import java.util.Optional;

public class ImportDeclarationMetaModel extends BaseNodeMetaModel {

    ImportDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.ImportDeclaration.class, "ImportDeclaration", "com.github.javaparser.ast.ImportDeclaration", "com.github.javaparser.ast", false);
    }
}

