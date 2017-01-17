package com.github.javaparser.metamodel;

import java.util.Optional;

public class InstanceOfExprMetaModel extends ClassMetaModel {

    public InstanceOfExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.InstanceOfExpr.class, "InstanceOfExpr", "com.github.javaparser.ast.expr.InstanceOfExpr", "com.github.javaparser.ast.expr", false);
    }
}

