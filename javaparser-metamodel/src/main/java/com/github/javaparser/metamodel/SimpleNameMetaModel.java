package com.github.javaparser.metamodel;

import java.util.Optional;

public class SimpleNameMetaModel extends BaseNodeMetaModel {

    SimpleNameMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SimpleName.class, "SimpleName", "com.github.javaparser.ast.expr.SimpleName", "com.github.javaparser.ast.expr", false);
    }
}

