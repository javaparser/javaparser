package com.github.javaparser.metamodel;

import java.util.Optional;

public class CommentMetaModel extends BaseNodeMetaModel {

    CommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments", true, false);
    }

    public PropertyMetaModel contentPropertyMetaModel;
}

