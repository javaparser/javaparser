package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceDeclarationMetaModel extends ClassMetaModel {

    public ClassOrInterfaceDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false);
    }
}

