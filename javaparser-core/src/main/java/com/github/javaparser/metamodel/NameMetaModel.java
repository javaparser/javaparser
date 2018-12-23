package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends NodeMetaModel {

    NameMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel identifierPropertyMetaModel;

    public PropertyMetaModel qualifierPropertyMetaModel;
}
