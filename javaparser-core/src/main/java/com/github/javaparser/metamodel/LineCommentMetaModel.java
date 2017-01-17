package com.github.javaparser.metamodel;

import java.util.Optional;

public class LineCommentMetaModel extends ClassMetaModel {

    public LineCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

