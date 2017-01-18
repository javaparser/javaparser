package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.AssignExpr;

public class AssignExprMetaModel extends ClassMetaModel {

    AssignExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr.AssignExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.AssignExpr.Operator.class, getField("operator"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTarget", "setTarget", "target", com.github.javaparser.ast.expr.Expression.class, getField("target"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, getField("value"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return AssignExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

