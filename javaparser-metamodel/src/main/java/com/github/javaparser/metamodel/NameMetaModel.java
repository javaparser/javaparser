package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameMetaModel extends BaseNodeMetaModel {

    NameMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Name.class, "Name", "com.github.javaparser.ast.expr.Name", "com.github.javaparser.ast.expr", false);
    }
}

