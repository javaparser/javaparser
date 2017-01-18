package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.LongLiteralExpr;

public class LongLiteralExprMetaModel extends ClassMetaModel {

    LongLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr.LongLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return LongLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

