package com.github.javaparser.metamodel;

import java.util.Optional;

public class FieldAccessExprMetaModel extends ClassMetaModel {

    public FieldAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.FieldAccessExpr.class, "FieldAccessExpr", "com.github.javaparser.ast.expr.FieldAccessExpr", "com.github.javaparser.ast.expr", false);
    }
}

