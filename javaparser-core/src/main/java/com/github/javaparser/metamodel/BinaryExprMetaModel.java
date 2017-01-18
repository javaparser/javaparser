package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.BinaryExpr;

public class BinaryExprMetaModel extends ClassMetaModel {

    BinaryExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.BinaryExpr.class, "BinaryExpr", "com.github.javaparser.ast.expr.BinaryExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getLeft", "setLeft", "left", com.github.javaparser.ast.expr.Expression.class, getField("left"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getOperator", "setOperator", "operator", com.github.javaparser.ast.expr.BinaryExpr.Operator.class, getField("operator"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getRight", "setRight", "right", com.github.javaparser.ast.expr.Expression.class, getField("right"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return BinaryExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

