package com.github.javaparser.metamodel;

import java.util.Optional;

public class NodeListMetaModel extends BaseNodeMetaModel {

    NodeListMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.NodeList.class, "NodeList", "com.github.javaparser.ast.NodeList", "com.github.javaparser.ast", false);
    }
}

