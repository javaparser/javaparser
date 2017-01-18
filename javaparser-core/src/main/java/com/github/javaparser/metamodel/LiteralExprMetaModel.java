package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.LiteralExpr;

public class LiteralExprMetaModel extends ClassMetaModel {

    LiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LiteralExpr.class, "LiteralExpr", "com.github.javaparser.ast.expr.LiteralExpr", "com.github.javaparser.ast.expr", true);
    }

    private Field getField(String name) {
        try {
            return LiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

