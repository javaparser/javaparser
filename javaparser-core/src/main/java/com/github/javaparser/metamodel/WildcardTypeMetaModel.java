package com.github.javaparser.metamodel;

import java.util.Optional;

public class WildcardTypeMetaModel extends TypeMetaModel {

    WildcardTypeMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.type.WildcardType.class, "WildcardType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel extendedTypePropertyMetaModel;

    public PropertyMetaModel superTypePropertyMetaModel;
}
