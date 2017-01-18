package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.Expression;

public class ExpressionMetaModel extends ClassMetaModel {

    ExpressionMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.Expression.class, "Expression", "com.github.javaparser.ast.expr.Expression", "com.github.javaparser.ast.expr", true);
    }

    private Field getField(String name) {
        try {
            return Expression.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

