package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThisExprMetaModel extends ClassMetaModel {

    public ThisExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ThisExpr.class, "ThisExpr", "com.github.javaparser.ast.expr.ThisExpr", "com.github.javaparser.ast.expr", false);
    }
}

