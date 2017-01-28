package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeParameterMetaModel extends BaseNodeMetaModel {

    TypeParameterMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.TypeParameter.class, "TypeParameter", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel typeBoundPropertyMetaModel;
}

