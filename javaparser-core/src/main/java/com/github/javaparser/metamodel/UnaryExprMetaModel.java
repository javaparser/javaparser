package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class UnaryExprMetaModel extends ClassMetaModel {

    UnaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr.UnaryExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.UnaryExpr.Operator.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return UnaryExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

