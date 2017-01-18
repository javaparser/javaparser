package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.ConditionalExpr;

public class ConditionalExprMetaModel extends ClassMetaModel {

    ConditionalExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ConditionalExpr.class, "ConditionalExpr", "com.github.javaparser.ast.expr.ConditionalExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getCondition", "setCondition", "condition", com.github.javaparser.ast.expr.Expression.class, getField("condition"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getElseExpr", "setElseExpr", "elseExpr", com.github.javaparser.ast.expr.Expression.class, getField("elseExpr"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getThenExpr", "setThenExpr", "thenExpr", com.github.javaparser.ast.expr.Expression.class, getField("thenExpr"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return ConditionalExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

