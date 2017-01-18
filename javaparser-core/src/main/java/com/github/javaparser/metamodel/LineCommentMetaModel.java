package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class LineCommentMetaModel extends ClassMetaModel {

    LineCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments.LineComment", "com.github.javaparser.ast.comments", false);
    }

    private Field getField(String name) {
        try {
            return LineCommentMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

