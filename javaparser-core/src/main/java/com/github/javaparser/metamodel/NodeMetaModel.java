package com.github.javaparser.metamodel;

import java.util.Optional;

public class NodeMetaModel extends ClassMetaModel {

    public NodeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.Node.class, "Node", "com.github.javaparser.ast.Node", "com.github.javaparser.ast", true);
    }
}

