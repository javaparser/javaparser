package com.github.javaparser.metamodel;

import java.util.Optional;

public class ExpressionMetaModel extends ClassMetaModel {

    public ExpressionMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, null, com.github.javaparser.ast.expr.Expression.class, "Expression", "com.github.javaparser.ast.expr.Expression", "com.github.javaparser.ast.expr", true);
    }
}

