package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends BaseNodeMetaModel {

    UnaryExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr.UnaryExpr", "com.github.javaparser.ast.expr", false);
    }
}

