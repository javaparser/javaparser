package com.github.javaparser.metamodel;

import java.util.Optional;

public class LongLiteralExprMetaModel extends ClassMetaModel {

    LongLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr.LongLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

