package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends BaseNodeMetaModel {

    NameMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel identifierPropertyMetaModel;

    public PropertyMetaModel qualifierPropertyMetaModel;
}

