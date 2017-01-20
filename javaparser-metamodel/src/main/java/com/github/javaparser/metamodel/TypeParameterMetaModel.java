package com.github.javaparser.metamodel;

import java.util.Optional;

public class TypeParameterMetaModel extends BaseNodeMetaModel {

    TypeParameterMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.TypeParameter.class, "TypeParameter", "com.github.javaparser.ast.type.TypeParameter", "com.github.javaparser.ast.type", false);
    }
}

