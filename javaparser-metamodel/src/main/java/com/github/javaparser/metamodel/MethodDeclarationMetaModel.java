package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodDeclarationMetaModel extends BaseNodeMetaModel {

    MethodDeclarationMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.MethodDeclaration.class, "MethodDeclaration", "com.github.javaparser.ast.body.MethodDeclaration", "com.github.javaparser.ast.body", false);
    }
}

