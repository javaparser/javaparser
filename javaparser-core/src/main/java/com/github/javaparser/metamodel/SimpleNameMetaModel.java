package com.github.javaparser.metamodel;

import java.util.Optional;

public class SimpleNameMetaModel extends BaseNodeMetaModel {

    SimpleNameMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.SimpleName.class, "SimpleName", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel identifierPropertyMetaModel;
}

