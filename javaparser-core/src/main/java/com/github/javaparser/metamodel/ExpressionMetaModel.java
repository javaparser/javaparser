package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ExpressionMetaModel extends ClassMetaModel {

    ExpressionMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Expression.class, "Expression", "com.github.javaparser.ast.expr.Expression", "com.github.javaparser.ast.expr", true);
    }

    private Field getField(String name) {
        try {
            return ExpressionMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

