package com.github.javaparser.metamodel;

import java.util.Optional;

public class EnclosedExprMetaModel extends ClassMetaModel {

    EnclosedExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.EnclosedExpr.class, "EnclosedExpr", "com.github.javaparser.ast.expr.EnclosedExpr", "com.github.javaparser.ast.expr", false);
    }
}

