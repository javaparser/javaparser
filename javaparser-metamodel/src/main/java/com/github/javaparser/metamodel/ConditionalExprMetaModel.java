package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConditionalExprMetaModel extends BaseNodeMetaModel {

    ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
    }
}

