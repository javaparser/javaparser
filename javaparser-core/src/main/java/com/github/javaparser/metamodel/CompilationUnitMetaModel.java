package com.github.javaparser.metamodel;

import java.util.Optional;

public class CompilationUnitMetaModel extends ClassMetaModel {

    public CompilationUnitMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.CompilationUnit.class, "CompilationUnit", "com.github.javaparser.ast.CompilationUnit", "com.github.javaparser.ast", false);
    }
}

