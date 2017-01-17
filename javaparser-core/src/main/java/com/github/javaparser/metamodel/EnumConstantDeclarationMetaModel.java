package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnumConstantDeclarationMetaModel extends ClassMetaModel {

    public EnumConstantDeclarationMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.EnumConstantDeclaration.class, "EnumConstantDeclaration", "com.github.javaparser.ast.body.EnumConstantDeclaration", "com.github.javaparser.ast.body", false);
    }
}

