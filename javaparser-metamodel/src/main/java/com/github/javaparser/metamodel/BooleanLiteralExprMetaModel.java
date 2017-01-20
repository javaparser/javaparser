package com.github.javaparser.metamodel;

import java.util.Optional;

public class BooleanLiteralExprMetaModel extends BaseNodeMetaModel {

    BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr.BooleanLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

