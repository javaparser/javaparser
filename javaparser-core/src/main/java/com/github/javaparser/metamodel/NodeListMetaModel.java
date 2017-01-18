package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class NodeListMetaModel extends ClassMetaModel {

    NodeListMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.NodeList.class, "NodeList", "com.github.javaparser.ast.NodeList", "com.github.javaparser.ast", false);
    }

    private Field getField(String name) {
        try {
            return NodeListMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

