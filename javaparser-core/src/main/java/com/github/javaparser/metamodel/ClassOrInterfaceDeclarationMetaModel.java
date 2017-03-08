package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassOrInterfaceDeclarationMetaModel extends TypeDeclarationMetaModel {

    ClassOrInterfaceDeclarationMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.body.ClassOrInterfaceDeclaration.class, "ClassOrInterfaceDeclaration", "com.github.javaparser.ast.body", false, false);
    }

    public PropertyMetaModel extendedTypesPropertyMetaModel;

    public PropertyMetaModel implementedTypesPropertyMetaModel;

    public PropertyMetaModel isInterfacePropertyMetaModel;

    public PropertyMetaModel typeParametersPropertyMetaModel;
}
