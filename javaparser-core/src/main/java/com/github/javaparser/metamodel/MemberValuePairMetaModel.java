package com.github.javaparser.metamodel;

import java.util.Optional;

public class MemberValuePairMetaModel extends ClassMetaModel {

    public MemberValuePairMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, null, null, null, null, false);
    }
}

