package com.github.javaparser.metamodel;

import java.util.Optional;

public class BreakStmtMetaModel extends ClassMetaModel {

    public BreakStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

