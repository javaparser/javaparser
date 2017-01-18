package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class LongLiteralExprMetaModel extends ClassMetaModel {

    LongLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.LongLiteralExpr.class, "LongLiteralExpr", "com.github.javaparser.ast.expr.LongLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return LongLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

