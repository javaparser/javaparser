package com.github.javaparser.metamodel;

import java.util.Optional;

public class SuperExprMetaModel extends ClassMetaModel {

    public SuperExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.SuperExpr.class, "SuperExpr", "com.github.javaparser.ast.expr.SuperExpr", "com.github.javaparser.ast.expr", false);
    }
}

