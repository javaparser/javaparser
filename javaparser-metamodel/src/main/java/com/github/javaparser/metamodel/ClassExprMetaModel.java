package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassExprMetaModel extends ClassMetaModel {

    ClassExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ClassExpr.class, "ClassExpr", "com.github.javaparser.ast.expr.ClassExpr", "com.github.javaparser.ast.expr", false);
    }
}

