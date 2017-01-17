package com.github.javaparser.metamodel;

import java.util.Optional;

public class BooleanLiteralExprMetaModel extends ClassMetaModel {

    public BooleanLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.BooleanLiteralExpr.class, "BooleanLiteralExpr", "com.github.javaparser.ast.expr.BooleanLiteralExpr", "com.github.javaparser.ast.expr", false);
    }
}

