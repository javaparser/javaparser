package com.github.javaparser.metamodel;

import java.util.Optional;

public class ObjectCreationExprMetaModel extends BaseNodeMetaModel {

    ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.ObjectCreationExpr.class, "ObjectCreationExpr", "com.github.javaparser.ast.expr.ObjectCreationExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel anonymousClassBodyPropertyMetaModel;

    public PropertyMetaModel argumentsPropertyMetaModel;

    public PropertyMetaModel scopePropertyMetaModel;

    public PropertyMetaModel typePropertyMetaModel;

    public PropertyMetaModel typeArgumentsPropertyMetaModel;
}

