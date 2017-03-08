package com.github.javaparser.metamodel;

import java.util.Optional;

public class SingleMemberAnnotationExprMetaModel extends AnnotationExprMetaModel {

    SingleMemberAnnotationExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel memberValuePropertyMetaModel;
}
