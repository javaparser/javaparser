package com.github.javaparser.metamodel;

import java.util.Optional;

public class TryStmtMetaModel extends ClassMetaModel {

    public TryStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

