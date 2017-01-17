package com.github.javaparser.metamodel;

import java.util.Optional;

public class EmptyStmtMetaModel extends ClassMetaModel {

    public EmptyStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

