package com.github.javaparser.metamodel;

import java.util.Optional;

public class StringLiteralExprMetaModel extends BaseNodeMetaModel {

    StringLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.StringLiteralExpr.class, "StringLiteralExpr", "com.github.javaparser.ast.expr.StringLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

