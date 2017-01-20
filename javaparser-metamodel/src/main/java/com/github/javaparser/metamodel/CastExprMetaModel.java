package com.github.javaparser.metamodel;

import java.util.Optional;

public class CastExprMetaModel extends BaseNodeMetaModel {

    CastExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.CastExpr.class, "CastExpr", "com.github.javaparser.ast.expr.CastExpr", "com.github.javaparser.ast.expr", false);
    }
}

