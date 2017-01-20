package com.github.javaparser.metamodel;

import java.util.Optional;

public class CharLiteralExprMetaModel extends BaseNodeMetaModel {

    CharLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.CharLiteralExpr.class, "CharLiteralExpr", "com.github.javaparser.ast.expr.CharLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

