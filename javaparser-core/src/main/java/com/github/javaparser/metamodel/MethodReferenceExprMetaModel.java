package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.MethodReferenceExpr;

public class MethodReferenceExprMetaModel extends ClassMetaModel {

    MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr.MethodReferenceExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, getField("identifier"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField("scope"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField("typeArguments"), true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return MethodReferenceExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

