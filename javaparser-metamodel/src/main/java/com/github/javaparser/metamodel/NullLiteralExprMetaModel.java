package com.github.javaparser.metamodel;

import java.util.Optional;

public class NullLiteralExprMetaModel extends ClassMetaModel {

    NullLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NullLiteralExpr.class, "NullLiteralExpr", "com.github.javaparser.ast.expr.NullLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

