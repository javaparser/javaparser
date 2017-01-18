package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.UnaryExpr;

public class UnaryExprMetaModel extends ClassMetaModel {

    UnaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.UnaryExpr.class, "UnaryExpr", "com.github.javaparser.ast.expr.UnaryExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, getField("expression"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.UnaryExpr.Operator.class, getField("operator"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return UnaryExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

