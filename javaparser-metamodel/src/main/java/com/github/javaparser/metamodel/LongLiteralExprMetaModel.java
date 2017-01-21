package com.github.javaparser.metamodel;

import java.util.Optional;

public class LongLiteralExprMetaModel extends BaseNodeMetaModel {

    LongLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}

