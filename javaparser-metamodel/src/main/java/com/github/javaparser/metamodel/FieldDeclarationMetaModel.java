package com.github.javaparser.metamodel;

import java.util.Optional;

public class FieldDeclarationMetaModel extends BaseNodeMetaModel {

    FieldDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.FieldDeclaration.class, "FieldDeclaration", "com.github.javaparser.ast.body.FieldDeclaration", "com.github.javaparser.ast.body", false);
    }
}

