package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends ClassMetaModel {

    public UnaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr.UnaryExpr", "com.github.javaparser.ast.expr", false);
    }
}

