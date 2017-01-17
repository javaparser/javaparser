package com.github.javaparser.metamodel;

import java.util.Optional;

public class WhileStmtMetaModel extends ClassMetaModel {

    public WhileStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

