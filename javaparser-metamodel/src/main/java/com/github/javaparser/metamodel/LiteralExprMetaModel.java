package com.github.javaparser.metamodel;

import java.util.Optional;

public class LiteralExprMetaModel extends BaseNodeMetaModel {

    LiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.LiteralExpr.class, "LiteralExpr", "com.github.javaparser.ast.expr.LiteralExpr", "com.github.javaparser.ast.expr", true);
    }
}

