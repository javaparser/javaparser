package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConditionalExprMetaModel extends ClassMetaModel {

    ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
    }
}

