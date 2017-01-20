package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameExprMetaModel extends ClassMetaModel {

    NameExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NameExpr.class, "NameExpr", "com.github.javaparser.ast.expr.NameExpr", "com.github.javaparser.ast.expr", false);
    }
}

