package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclaratorMetaModel extends ClassMetaModel {

    public VariableDeclaratorMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

