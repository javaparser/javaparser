package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class SingleMemberAnnotationExprMetaModel extends ClassMetaModel {

    SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr.SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getMemberValue", "setMemberValue", "memberValue", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SingleMemberAnnotationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

