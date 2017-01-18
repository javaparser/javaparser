package com.github.javaparser.metamodel;

import java.util.Optional;

public class IntegerLiteralExprMetaModel extends ClassMetaModel {

    IntegerLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.IntegerLiteralExpr.class, "IntegerLiteralExpr", "com.github.javaparser.ast.expr.IntegerLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

