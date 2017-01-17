package com.github.javaparser.metamodel;

import java.util.Optional;

public class BlockStmtMetaModel extends ClassMetaModel {

    public BlockStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

