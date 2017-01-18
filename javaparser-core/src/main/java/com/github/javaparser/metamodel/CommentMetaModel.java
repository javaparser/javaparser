package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.comments.Comment;

public class CommentMetaModel extends ClassMetaModel {

    CommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments.Comment", "com.github.javaparser.ast.comments", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getCommentedNode", "setCommentedNode", "commentedNode", com.github.javaparser.ast.Node.class, getField("commentedNode"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getContent", "setContent", "content", java.lang.String.class, getField("content"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return Comment.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

