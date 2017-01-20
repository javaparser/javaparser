package com.github.javaparser.metamodel;

import java.util.Optional;

public class NameExprMetaModel extends BaseNodeMetaModel {

    NameExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.NameExpr.class, "NameExpr", "com.github.javaparser.ast.expr.NameExpr", "com.github.javaparser.ast.expr", false);
    }
}

