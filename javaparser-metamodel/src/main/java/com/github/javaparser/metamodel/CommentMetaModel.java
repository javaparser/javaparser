package com.github.javaparser.metamodel;

import java.util.Optional;

public class CommentMetaModel extends BaseNodeMetaModel {

    CommentMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments", true, false);
    }

    public PropertyMetaModel commentedNodePropertyMetaModel;

    public PropertyMetaModel contentPropertyMetaModel;
}

