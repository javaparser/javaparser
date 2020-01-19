package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends CommentMetaModel {

    LineCommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments", false, false);
    }
}
