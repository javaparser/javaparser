package com.github.javaparser.metamodel;

import java.util.Optional;

public class CommentMetaModel extends ClassMetaModel {

    public CommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

