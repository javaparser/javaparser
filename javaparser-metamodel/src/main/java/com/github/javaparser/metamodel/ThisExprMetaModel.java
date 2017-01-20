package com.github.javaparser.metamodel;

import java.util.Optional;

public class ThisExprMetaModel extends BaseNodeMetaModel {

    ThisExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ThisExpr.class, "ThisExpr", "com.github.javaparser.ast.expr.ThisExpr", "com.github.javaparser.ast.expr", false);
    }
}

