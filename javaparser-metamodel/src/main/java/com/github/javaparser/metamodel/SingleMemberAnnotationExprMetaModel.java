package com.github.javaparser.metamodel;

import java.util.Optional;

public class SingleMemberAnnotationExprMetaModel extends BaseNodeMetaModel {

    SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr.SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }
}

