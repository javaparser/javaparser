package com.github.javaparser.metamodel;

import java.util.Optional;

public class BinaryExprMetaModel extends ClassMetaModel {

    public BinaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.BinaryExpr.class, "BinaryExpr", "com.github.javaparser.ast.expr.BinaryExpr", "com.github.javaparser.ast.expr", false);
    }
}

