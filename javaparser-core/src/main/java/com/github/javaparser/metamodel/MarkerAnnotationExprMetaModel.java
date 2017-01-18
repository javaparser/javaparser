package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;

public class MarkerAnnotationExprMetaModel extends ClassMetaModel {

    MarkerAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MarkerAnnotationExpr.class, "MarkerAnnotationExpr", "com.github.javaparser.ast.expr.MarkerAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return MarkerAnnotationExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

