package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceDeclarationMetaModel extends BaseNodeMetaModel {

    ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false);
    }
}

