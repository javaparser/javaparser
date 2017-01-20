package com.github.javaparser.metamodel;

import java.util.Optional;

public class ClassExprMetaModel extends BaseNodeMetaModel {

    ClassExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.ClassExpr.class, "ClassExpr", "com.github.javaparser.ast.expr.ClassExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel typePropertyMetaModel;
}

