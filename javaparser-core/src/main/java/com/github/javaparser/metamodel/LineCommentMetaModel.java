package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends BaseNodeMetaModel {

    LineCommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments", false, false);
    }
}

