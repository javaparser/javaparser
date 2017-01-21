package com.github.javaparser.metamodel;

import java.util.Optional;

public class AssignExprMetaModel extends BaseNodeMetaModel {

    AssignExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel operatorPropertyMetaModel;

    public PropertyMetaModel targetPropertyMetaModel;

    public PropertyMetaModel valuePropertyMetaModel;
}

