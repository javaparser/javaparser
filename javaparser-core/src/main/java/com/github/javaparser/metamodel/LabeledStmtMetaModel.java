package com.github.javaparser.metamodel;

import java.util.Optional;

public class LabeledStmtMetaModel extends ClassMetaModel {

    public LabeledStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

