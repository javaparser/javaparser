package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExplicitConstructorInvocationStmtMetaModel extends ClassMetaModel {

    public ExplicitConstructorInvocationStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

