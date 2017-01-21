package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends BaseNodeMetaModel {

    LineCommentMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments", false, false);
    }
}

