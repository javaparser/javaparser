package com.github.javaparser.metamodel;

import java.util.Optional;

public class DoubleLiteralExprMetaModel extends BaseNodeMetaModel {

    DoubleLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.DoubleLiteralExpr.class, "DoubleLiteralExpr", "com.github.javaparser.ast.expr.DoubleLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

