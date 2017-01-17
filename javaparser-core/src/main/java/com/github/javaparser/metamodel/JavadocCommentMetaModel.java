package com.github.javaparser.metamodel;

import java.util.Optional;

public class JavadocCommentMetaModel extends ClassMetaModel {

    public JavadocCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

