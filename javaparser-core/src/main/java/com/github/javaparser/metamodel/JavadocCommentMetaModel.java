package com.github.javaparser.metamodel;

import java.util.Optional;

public class JavadocCommentMetaModel extends CommentMetaModel {

    JavadocCommentMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.comments.JavadocComment.class, "JavadocComment", "com.github.javaparser.ast.comments", false, false);
    }
}
