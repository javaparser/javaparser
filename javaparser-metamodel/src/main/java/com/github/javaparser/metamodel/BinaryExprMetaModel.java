package com.github.javaparser.metamodel;

import java.util.Optional;

public class BinaryExprMetaModel extends BaseNodeMetaModel {

    BinaryExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.BinaryExpr.class, "BinaryExpr", "com.github.javaparser.ast.expr.BinaryExpr", "com.github.javaparser.ast.expr", false);
    }
}

