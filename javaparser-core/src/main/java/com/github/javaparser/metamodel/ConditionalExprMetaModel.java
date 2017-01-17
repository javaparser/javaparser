package com.github.javaparser.metamodel;

import java.util.Optional;

public class ConditionalExprMetaModel extends ClassMetaModel {

    public ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
    }
}

