package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class NodeMetaModel extends ClassMetaModel {

    NodeMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.Node.class, "Node", "com.github.javaparser.ast.Node", "com.github.javaparser.ast", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getComment", "setComment", "comment", com.github.javaparser.ast.comments.Comment.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return NodeMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

