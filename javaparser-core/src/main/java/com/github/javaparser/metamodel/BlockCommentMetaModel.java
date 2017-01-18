package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class BlockCommentMetaModel extends ClassMetaModel {

    BlockCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.BlockComment.class, "BlockComment", "com.github.javaparser.ast.comments.BlockComment", "com.github.javaparser.ast.comments", false);
    }

    private Field getField(String name) {
        try {
            return BlockCommentMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

