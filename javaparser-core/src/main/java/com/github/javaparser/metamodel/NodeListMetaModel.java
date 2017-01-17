package com.github.javaparser.metamodel;

import java.util.Optional;

public class NodeListMetaModel extends ClassMetaModel {

    public NodeListMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.NodeList.class, "NodeList", "com.github.javaparser.ast.NodeList", "com.github.javaparser.ast", false);
    }
}

