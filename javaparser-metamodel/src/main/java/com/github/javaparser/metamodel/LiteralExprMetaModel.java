package com.github.javaparser.metamodel;

import java.util.Optional;

public class LiteralExprMetaModel extends ClassMetaModel {

    LiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LiteralExpr.class, "LiteralExpr", "com.github.javaparser.ast.expr.LiteralExpr", "com.github.javaparser.ast.expr", true);
    }
}

