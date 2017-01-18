package com.github.javaparser.metamodel;

import java.util.Optional;

public class CastExprMetaModel extends ClassMetaModel {

    CastExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.CastExpr.class, "CastExpr", "com.github.javaparser.ast.expr.CastExpr", "com.github.javaparser.ast.expr", false);
    }
}

