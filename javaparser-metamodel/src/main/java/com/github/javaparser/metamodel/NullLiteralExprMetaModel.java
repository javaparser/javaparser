package com.github.javaparser.metamodel;

import java.util.Optional;

public class NullLiteralExprMetaModel extends BaseNodeMetaModel {

    NullLiteralExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NullLiteralExpr.class, "NullLiteralExpr", "com.github.javaparser.ast.expr.NullLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

