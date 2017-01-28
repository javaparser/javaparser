package com.github.javaparser.metamodel;

import java.util.Optional;

public class CompilationUnitMetaModel extends BaseNodeMetaModel {

    CompilationUnitMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast", false, false);
    }

    public PropertyMetaModel importsPropertyMetaModel;

    public PropertyMetaModel packageDeclarationPropertyMetaModel;

    public PropertyMetaModel typesPropertyMetaModel;
}

