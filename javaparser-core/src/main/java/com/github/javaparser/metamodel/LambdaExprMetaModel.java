package com.github.javaparser.metamodel;

import java.util.Optional;

public class LambdaExprMetaModel extends ExpressionMetaModel {

    LambdaExprMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.expr.LambdaExpr.class, "LambdaExpr", "com.github.javaparser.ast.expr", false, false);
    }

    public PropertyMetaModel bodyPropertyMetaModel;

    public PropertyMetaModel isEnclosingParametersPropertyMetaModel;

    public PropertyMetaModel parametersPropertyMetaModel;

    public PropertyMetaModel expressionBodyPropertyMetaModel;
}
