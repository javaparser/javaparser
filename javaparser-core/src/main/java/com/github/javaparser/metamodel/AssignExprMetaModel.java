package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class AssignExprMetaModel extends ClassMetaModel {

    AssignExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AssignExpr.class, "AssignExpr", "com.github.javaparser.ast.expr.AssignExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.AssignExpr.Operator.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTarget", "setTarget", "target", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getValue", "setValue", "value", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return AssignExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

