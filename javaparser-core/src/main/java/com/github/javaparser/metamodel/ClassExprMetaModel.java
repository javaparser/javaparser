package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassExprMetaModel extends ClassMetaModel {

    public ClassExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.ClassExpr.class, "ClassExpr", "com.github.javaparser.ast.expr.ClassExpr", "com.github.javaparser.ast.expr", false);
    }
}

