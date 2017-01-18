package com.github.javaparser.metamodel;

import java.util.Optional;

public class UnaryExprMetaModel extends ClassMetaModel {

    UnaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr.UnaryExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", int.class, null, true, false, false, false));
    }
}

