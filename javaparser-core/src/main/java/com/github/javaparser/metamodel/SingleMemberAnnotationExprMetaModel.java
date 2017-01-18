package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;

public class SingleMemberAnnotationExprMetaModel extends ClassMetaModel {

    SingleMemberAnnotationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.SingleMemberAnnotationExpr.class, "SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr.SingleMemberAnnotationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getMemberValue", "setMemberValue", "memberValue", com.github.javaparser.ast.expr.Expression.class, getField("memberValue"), true, false, false, false, false));
    }

    private Field getField(String name) {
        try {
            return SingleMemberAnnotationExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

