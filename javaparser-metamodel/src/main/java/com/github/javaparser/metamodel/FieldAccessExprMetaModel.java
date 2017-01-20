package com.github.javaparser.metamodel;

import java.util.Optional;

public class FieldAccessExprMetaModel extends BaseNodeMetaModel {

    FieldAccessExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.FieldAccessExpr.class, "FieldAccessExpr", "com.github.javaparser.ast.expr.FieldAccessExpr", "com.github.javaparser.ast.expr", false);
    }
}

