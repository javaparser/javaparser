package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockCommentMetaModel extends CommentMetaModel {

    BlockCommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.BlockComment.class, "BlockComment", "com.github.javaparser.ast.comments", false, false);
    }
}
