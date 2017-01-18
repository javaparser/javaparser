package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class AnnotationExprMetaModel extends ClassMetaModel {

    AnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.AnnotationExpr.class, "AnnotationExpr", "com.github.javaparser.ast.expr.AnnotationExpr", "com.github.javaparser.ast.expr", true);
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.Name.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return AnnotationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

