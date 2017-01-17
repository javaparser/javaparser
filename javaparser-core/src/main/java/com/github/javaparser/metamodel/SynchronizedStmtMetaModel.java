package com.github.javaparser.metamodel;

import java.util.Optional;

public class SynchronizedStmtMetaModel extends ClassMetaModel {

    public SynchronizedStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

