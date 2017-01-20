package com.github.javaparser.metamodel;

import java.util.Optional;

public class JavadocCommentMetaModel extends BaseNodeMetaModel {

    JavadocCommentMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.JavadocComment.class, "JavadocComment", "com.github.javaparser.ast.comments.JavadocComment", "com.github.javaparser.ast.comments", false);
    }
}

