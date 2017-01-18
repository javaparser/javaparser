package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class JavadocCommentMetaModel extends ClassMetaModel {

    JavadocCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.JavadocComment.class, "JavadocComment", "com.github.javaparser.ast.comments.JavadocComment", "com.github.javaparser.ast.comments", false);
    }

    private Field getField(String name) {
        try {
            return JavadocCommentMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

