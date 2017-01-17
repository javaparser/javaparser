package com.github.javaparser.metamodel;

import java.util.Optional;

public class ImportDeclarationMetaModel extends ClassMetaModel {

    public ImportDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.ImportDeclaration.class, "ImportDeclaration", "com.github.javaparser.ast.ImportDeclaration", "com.github.javaparser.ast", false);
    }
}

