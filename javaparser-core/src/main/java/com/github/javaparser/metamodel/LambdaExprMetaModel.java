package com.github.javaparser.metamodel;

import java.util.Optional;

public class LambdaExprMetaModel extends ClassMetaModel {

    public LambdaExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.LambdaExpr.class, "LambdaExpr", "com.github.javaparser.ast.expr.LambdaExpr", "com.github.javaparser.ast.expr", false);
    }
}

