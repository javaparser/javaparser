package com.github.javaparser.metamodel;

import java.util.Optional;

public class CommentMetaModel extends ClassMetaModel {

    public CommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments.Comment", "com.github.javaparser.ast.comments", true);
    }
}

