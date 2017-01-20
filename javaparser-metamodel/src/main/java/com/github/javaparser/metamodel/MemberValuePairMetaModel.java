package com.github.javaparser.metamodel;

import java.util.Optional;

public class MemberValuePairMetaModel extends BaseNodeMetaModel {

    MemberValuePairMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.MemberValuePair.class, "MemberValuePair", "com.github.javaparser.ast.expr.MemberValuePair", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel valuePropertyMetaModel;
}

