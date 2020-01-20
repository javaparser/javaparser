package com.github.javaparser.metamodel;

import java.util.Optional;

public class SwitchExprMetaModel extends ExpressionMetaModel {

    SwitchExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.SwitchExpr.class, "SwitchExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel entriesPropertyMetaModel;

    public PropertyMetaModel selectorPropertyMetaModel;
}
