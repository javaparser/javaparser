package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssertStmtMetaModel extends ClassMetaModel {

    public AssertStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

