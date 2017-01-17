package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThrowStmtMetaModel extends ClassMetaModel {

    public ThrowStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

