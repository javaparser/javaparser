package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclaratorMetaModel extends ClassMetaModel {

    VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.body.VariableDeclarator.class, "VariableDeclarator", "com.github.javaparser.ast.body.VariableDeclarator", "com.github.javaparser.ast.body", false);
    }
}

