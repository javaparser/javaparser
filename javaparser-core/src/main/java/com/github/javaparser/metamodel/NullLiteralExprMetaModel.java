package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class NullLiteralExprMetaModel extends ClassMetaModel {

    NullLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NullLiteralExpr.class, "NullLiteralExpr", "com.github.javaparser.ast.expr.NullLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return NullLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

