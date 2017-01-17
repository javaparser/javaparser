package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameExprMetaModel extends ClassMetaModel {

    public NameExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.NameExpr.class, "NameExpr", "com.github.javaparser.ast.expr.NameExpr", "com.github.javaparser.ast.expr", false);
    }
}

