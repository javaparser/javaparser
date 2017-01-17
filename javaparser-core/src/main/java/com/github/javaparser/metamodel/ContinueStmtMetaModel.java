package com.github.javaparser.metamodel;

import java.util.Optional;

public class ContinueStmtMetaModel extends ClassMetaModel {

    public ContinueStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

