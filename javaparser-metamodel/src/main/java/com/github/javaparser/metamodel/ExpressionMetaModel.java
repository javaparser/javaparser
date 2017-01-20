package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionMetaModel extends BaseNodeMetaModel {

    ExpressionMetaModel(JavaParserMetaModel parent, Optional<BaseNodeMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Expression.class, "Expression", "com.github.javaparser.ast.expr.Expression", "com.github.javaparser.ast.expr", true);
    }
}

