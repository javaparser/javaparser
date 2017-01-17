package com.github.javaparser.metamodel;

import java.util.Optional;

public class ReturnStmtMetaModel extends ClassMetaModel {

    public ReturnStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

