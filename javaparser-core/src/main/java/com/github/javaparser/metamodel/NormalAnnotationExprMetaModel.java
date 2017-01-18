package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class NormalAnnotationExprMetaModel extends ClassMetaModel {

    NormalAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.NormalAnnotationExpr.class, "NormalAnnotationExpr", "com.github.javaparser.ast.expr.NormalAnnotationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getPairs", "setPairs", "pairs", com.github.javaparser.ast.expr.MemberValuePair.class, null, true, false, true, false, false));
    }

    private Field getField(String name) {
        try {
            return NormalAnnotationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

