package com.github.javaparser.metamodel;

import java.util.Optional;

public class CompilationUnitMetaModel extends BaseNodeMetaModel {

    CompilationUnitMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast.CompilationUnit", "com.github.javaparser.ast", false);
    }
}

