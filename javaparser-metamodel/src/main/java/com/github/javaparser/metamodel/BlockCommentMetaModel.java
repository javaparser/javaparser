package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockCommentMetaModel extends BaseNodeMetaModel {

    BlockCommentMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.comments.BlockComment.class, "BlockComment", "com.github.javaparser.ast.comments", false, false);
    }
}

