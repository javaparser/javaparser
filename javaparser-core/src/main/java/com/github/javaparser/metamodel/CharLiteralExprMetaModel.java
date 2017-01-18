package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class CharLiteralExprMetaModel extends ClassMetaModel {

    CharLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.CharLiteralExpr.class, "CharLiteralExpr", "com.github.javaparser.ast.expr.CharLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return CharLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

