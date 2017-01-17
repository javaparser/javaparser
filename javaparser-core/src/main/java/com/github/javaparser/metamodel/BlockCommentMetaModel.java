package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockCommentMetaModel extends ClassMetaModel {

    public BlockCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.comments.BlockComment.class, "BlockComment", "com.github.javaparser.ast.comments.BlockComment", "com.github.javaparser.ast.comments", false);
    }
}

