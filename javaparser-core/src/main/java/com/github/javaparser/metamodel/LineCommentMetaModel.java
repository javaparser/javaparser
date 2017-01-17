package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends ClassMetaModel {

    public LineCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.comments.LineComment.class, "LineComment", "com.github.javaparser.ast.comments.LineComment", "com.github.javaparser.ast.comments", false);
    }
}

