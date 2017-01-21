package com.github.javaparser.metamodel;

import java.util.Optional;

public class JavadocCommentMetaModel extends BaseNodeMetaModel {

    JavadocCommentMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.comments.JavadocComment.class, "JavadocComment", "com.github.javaparser.ast.comments", false);
    }
}

