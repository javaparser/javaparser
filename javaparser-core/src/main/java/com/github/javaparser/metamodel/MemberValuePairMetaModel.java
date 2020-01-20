package com.github.javaparser.metamodel;

import java.util.Optional;

public class MemberValuePairMetaModel extends NodeMetaModel {

    MemberValuePairMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.MemberValuePair.class, "MemberValuePair", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel namePropertyMetaModel;

    public PropertyMetaModel valuePropertyMetaModel;
}
