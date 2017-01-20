package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceTypeMetaModel extends BaseNodeMetaModel {

    ClassOrInterfaceTypeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.type.ClassOrInterfaceType.class, "ClassOrInterfaceType", "com.github.javaparser.ast.type.ClassOrInterfaceType", "com.github.javaparser.ast.type", false);
    }
}

