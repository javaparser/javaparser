package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;

public class IntegerLiteralExprMetaModel extends ClassMetaModel {

    IntegerLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.IntegerLiteralExpr.class, "IntegerLiteralExpr", "com.github.javaparser.ast.expr.IntegerLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return IntegerLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

