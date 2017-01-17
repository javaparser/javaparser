package com.github.javaparser.metamodel;

import java.util.Optional;

public class MemberValuePairMetaModel extends ClassMetaModel {

    public MemberValuePairMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.MemberValuePair.class, "MemberValuePair", "com.github.javaparser.ast.expr.MemberValuePair", "com.github.javaparser.ast.expr", false);
    }
}

