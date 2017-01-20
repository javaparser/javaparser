package com.github.javaparser.metamodel;

import java.util.Optional;

public class NodeMetaModel extends BaseNodeMetaModel {

    NodeMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.Node.class, "Node", "com.github.javaparser.ast.Node", "com.github.javaparser.ast", true);
    }
}

