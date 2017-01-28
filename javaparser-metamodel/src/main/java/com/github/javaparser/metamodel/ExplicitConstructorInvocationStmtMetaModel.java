package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExplicitConstructorInvocationStmtMetaModel extends BaseNodeMetaModel {

    ExplicitConstructorInvocationStmtMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt.class, "ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt", false, false);
    }

    public PropertyMetaModel argumentsPropertyMetaModel;

    public PropertyMetaModel expressionPropertyMetaModel;

    public PropertyMetaModel isThisPropertyMetaModel;

    public PropertyMetaModel typeArgumentsPropertyMetaModel;
}

