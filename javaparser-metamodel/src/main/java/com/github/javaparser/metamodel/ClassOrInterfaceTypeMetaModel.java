package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceTypeMetaModel extends BaseNodeMetaModel {

    ClassOrInterfaceTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.type.ClassOrInterfaceType.class, "ClassOrInterfaceType", "com.github.javaparser.ast.type", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel scopePropertyMetaModel;

    public PropertyMetaModel typeArgumentsPropertyMetaModel;
}

