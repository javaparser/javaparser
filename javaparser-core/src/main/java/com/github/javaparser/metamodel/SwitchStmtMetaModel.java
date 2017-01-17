package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchStmtMetaModel extends ClassMetaModel {

    public SwitchStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

