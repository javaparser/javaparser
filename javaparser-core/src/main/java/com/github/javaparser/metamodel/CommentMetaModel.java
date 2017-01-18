package com.github.javaparser.metamodel;

import java.util.Optional;

public class CommentMetaModel extends ClassMetaModel {

    CommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.comments.Comment.class, "Comment", "com.github.javaparser.ast.comments.Comment", "com.github.javaparser.ast.comments", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getCommentedNode", "setCommentedNode", "commentedNode", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getContent", "setContent", "content", int.class, null, true, false, false, false));
    }
}

