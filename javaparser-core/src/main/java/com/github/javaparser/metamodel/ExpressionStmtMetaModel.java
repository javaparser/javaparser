package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionStmtMetaModel extends ClassMetaModel {

    public ExpressionStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

