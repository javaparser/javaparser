package com.github.javaparser.metamodel;

import java.util.Optional;

public class CompilationUnitMetaModel extends NodeMetaModel {

    CompilationUnitMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast", false, false);
    }

    public PropertyMetaModel importsPropertyMetaModel;

    public PropertyMetaModel modulePropertyMetaModel;

    public PropertyMetaModel packageDeclarationPropertyMetaModel;

    public PropertyMetaModel typesPropertyMetaModel;
}
