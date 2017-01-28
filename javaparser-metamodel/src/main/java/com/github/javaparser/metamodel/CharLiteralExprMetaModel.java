package com.github.javaparser.metamodel;

import java.util.Optional;

public class CharLiteralExprMetaModel extends BaseNodeMetaModel {

    CharLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.CharLiteralExpr.class, "CharLiteralExpr", "com.github.javaparser.ast.expr", false, false);
    }
}

