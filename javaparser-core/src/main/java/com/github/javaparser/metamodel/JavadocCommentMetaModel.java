package com.github.javaparser.metamodel;

import java.util.Optional;

public class JavadocCommentMetaModel extends ClassMetaModel {

    JavadocCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.JavadocComment.class, "JavadocComment", "com.github.javaparser.ast.comments.JavadocComment", "com.github.javaparser.ast.comments", false);
    }
}

