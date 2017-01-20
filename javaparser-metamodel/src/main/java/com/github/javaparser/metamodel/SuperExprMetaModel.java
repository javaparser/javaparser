package com.github.javaparser.metamodel;

import java.util.Optional;

public class SuperExprMetaModel extends BaseNodeMetaModel {

    SuperExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SuperExpr.class, "SuperExpr", "com.github.javaparser.ast.expr.SuperExpr", "com.github.javaparser.ast.expr", false);
    }
}

