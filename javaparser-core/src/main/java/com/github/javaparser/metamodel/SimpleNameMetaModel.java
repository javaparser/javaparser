package com.github.javaparser.metamodel;

import java.util.Optional;

public class SimpleNameMetaModel extends ClassMetaModel {

    SimpleNameMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SimpleName.class, "SimpleName", "com.github.javaparser.ast.expr.SimpleName", "com.github.javaparser.ast.expr", false);
    }
}

