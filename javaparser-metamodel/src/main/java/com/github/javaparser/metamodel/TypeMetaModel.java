package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeMetaModel extends BaseNodeMetaModel {

    TypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.Type.class, "Type", "com.github.javaparser.ast.type", true);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;
}

