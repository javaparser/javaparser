package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class IntegerLiteralExprMetaModel extends ClassMetaModel {

    IntegerLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.IntegerLiteralExpr.class, "IntegerLiteralExpr", "com.github.javaparser.ast.expr.IntegerLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return IntegerLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

