package com.github.javaparser.metamodel;

import java.util.Optional;

public class SimpleNameMetaModel extends BaseNodeMetaModel {

    SimpleNameMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.SimpleName.class, "SimpleName", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel identifierPropertyMetaModel;
}

