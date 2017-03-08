package com.github.javaparser.metamodel;

import java.util.Optional;
import com.github.javaparser.ast.Node;

public class CommentMetaModel extends NodeMetaModel {

    CommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments", true, false);
    }

    protected CommentMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {
        super(superNodeMetaModel, type, name, packageName, isAbstract, hasWildcard);
    }

    public PropertyMetaModel contentPropertyMetaModel;
}
