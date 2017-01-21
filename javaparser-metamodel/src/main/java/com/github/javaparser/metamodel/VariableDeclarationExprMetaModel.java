package com.github.javaparser.metamodel;

import java.util.Optional;

public class VariableDeclarationExprMetaModel extends BaseNodeMetaModel {

    VariableDeclarationExprMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superBaseNodeMetaModel) {
        super(superBaseNodeMetaModel, parent, com.github.javaparser.ast.expr.VariableDeclarationExpr.class, "VariableDeclarationExpr", "com.github.javaparser.ast.expr", false);
    }

    public PropertyMetaModel annotationsPropertyMetaModel;

    public PropertyMetaModel modifiersPropertyMetaModel;

    public PropertyMetaModel variablesPropertyMetaModel;
}

