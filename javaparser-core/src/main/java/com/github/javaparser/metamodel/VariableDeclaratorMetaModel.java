package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclaratorMetaModel extends ClassMetaModel {

    public VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.body.VariableDeclarator.class, "VariableDeclarator", "com.github.javaparser.ast.body.VariableDeclarator", "com.github.javaparser.ast.body", false);
    }
}

