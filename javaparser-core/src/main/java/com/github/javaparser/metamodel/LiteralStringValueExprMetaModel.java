package com.github.javaparser.metamodel;

import java.util.Optional;
import com.github.javaparser.ast.Node;

public class LiteralStringValueExprMetaModel extends LiteralExprMetaModel {

    LiteralStringValueExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.LiteralStringValueExpr.class, "LiteralStringValueExpr", "com.github.javaparser.ast.expr", true, false);
    }

    protected LiteralStringValueExprMetaModel(Optional<BaseNodeMetaModel> superNodeMetaModel, Class<? extends Node> type, String name, String packageName, boolean isAbstract, boolean hasWildcard) {
        super(superNodeMetaModel, type, name, packageName, isAbstract, hasWildcard);
    }

    public PropertyMetaModel valuePropertyMetaModel;
}
