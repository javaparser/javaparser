package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockCommentMetaModel extends ClassMetaModel {

    public BlockCommentMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

