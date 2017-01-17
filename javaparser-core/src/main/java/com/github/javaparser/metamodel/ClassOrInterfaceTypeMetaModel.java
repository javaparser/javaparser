package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceTypeMetaModel extends ClassMetaModel {

    public ClassOrInterfaceTypeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.type.ClassOrInterfaceType.class, "ClassOrInterfaceType", "com.github.javaparser.ast.type.ClassOrInterfaceType", "com.github.javaparser.ast.type", false);
    }
}

