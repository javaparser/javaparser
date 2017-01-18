package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class DoubleLiteralExprMetaModel extends ClassMetaModel {

    DoubleLiteralExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.DoubleLiteralExpr.class, "DoubleLiteralExpr", "com.github.javaparser.ast.expr.DoubleLiteralExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return DoubleLiteralExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

