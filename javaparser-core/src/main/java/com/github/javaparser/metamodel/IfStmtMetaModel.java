package com.github.javaparser.metamodel;

import java.util.Optional;

public class IfStmtMetaModel extends ClassMetaModel {

    public IfStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

