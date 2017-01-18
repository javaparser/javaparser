package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.DoubleLiteralExpr;

public class DoubleLiteralExprMetaModel extends ClassMetaModel {

    DoubleLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.DoubleLiteralExpr.class, "DoubleLiteralExpr", "com.github.javaparser.ast.expr.DoubleLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return DoubleLiteralExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

