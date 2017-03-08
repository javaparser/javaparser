package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExplicitConstructorInvocationStmtMetaModel extends StatementMetaModel {

    ExplicitConstructorInvocationStmtMetaModel(Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt.class, "ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel argumentsPropertyMetaModel;

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel isThisPropertyMetaModel;

    public PropertyMetaModel typeArgumentsPropertyMetaModel;

    public PropertyMetaModel usingDiamondOperatorPropertyMetaModel;
}
