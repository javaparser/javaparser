package com.github.javaparser.metamodel;

import java.util.Optional;

public class LongLiteralExprMetaModel extends BaseNodeMetaModel {

    LongLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr.LongLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

