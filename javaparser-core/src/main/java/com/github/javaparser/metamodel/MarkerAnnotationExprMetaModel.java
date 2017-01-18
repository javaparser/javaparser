package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class MarkerAnnotationExprMetaModel extends ClassMetaModel {

    MarkerAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MarkerAnnotationExpr.class, "MarkerAnnotationExpr", "com.github.javaparser.ast.expr.MarkerAnnotationExpr", "com.github.javaparser.ast.expr", false);
    }

    private Field getField(String name) {
        try {
            return MarkerAnnotationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

