package com.github.javaparser.metamodel;

import java.util.Optional;

public class LiteralExprMetaModel extends ClassMetaModel {

    public LiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.LiteralExpr.class, "LiteralExpr", "com.github.javaparser.ast.expr.LiteralExpr", "com.github.javaparser.ast.expr", true);
    }
}

