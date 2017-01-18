package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends ClassMetaModel {

    LineCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments.LineComment", "com.github.javaparser.ast.comments", false);
    }
}

