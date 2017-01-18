package com.github.javaparser.metamodel;

import java.util.Optional;

public class NodeMetaModel extends ClassMetaModel {

    NodeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.Node.class, "Node", "com.github.javaparser.ast.Node", "com.github.javaparser.ast", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getComment", "setComment", "comment", int.class, null, true, false, false, false));
    }
}

