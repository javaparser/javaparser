package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssignExprMetaModel extends BaseNodeMetaModel {

    AssignExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr.AssignExpr", "com.github.javaparser.ast.expr", false);
    }
}

