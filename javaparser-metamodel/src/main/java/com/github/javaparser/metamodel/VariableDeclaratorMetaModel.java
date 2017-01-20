package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclaratorMetaModel extends BaseNodeMetaModel {

    VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.body.VariableDeclarator.class, "VariableDeclarator", "com.github.javaparser.ast.body.VariableDeclarator", "com.github.javaparser.ast.body", false);
    }
}

