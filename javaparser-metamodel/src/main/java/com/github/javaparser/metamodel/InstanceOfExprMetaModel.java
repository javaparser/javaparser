package com.github.javaparser.metamodel;

import java.util.Optional;

public class InstanceOfExprMetaModel extends ClassMetaModel {

    InstanceOfExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.InstanceOfExpr.class, "InstanceOfExpr", "com.github.javaparser.ast.expr.InstanceOfExpr", "com.github.javaparser.ast.expr", false);
    }
}

