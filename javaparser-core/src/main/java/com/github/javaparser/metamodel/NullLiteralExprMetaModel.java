package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.NullLiteralExpr;

public class NullLiteralExprMetaModel extends ClassMetaModel {

    NullLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NullLiteralExpr.class, "NullLiteralExpr", "com.github.javaparser.ast.expr.NullLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return NullLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

