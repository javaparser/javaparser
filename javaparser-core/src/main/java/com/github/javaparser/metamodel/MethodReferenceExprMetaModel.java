package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class MethodReferenceExprMetaModel extends ClassMetaModel {

    MethodReferenceExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodReferenceExpr.class, "MethodReferenceExpr", "com.github.javaparser.ast.expr.MethodReferenceExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getIdentifier", "setIdentifier", "identifier", java.lang.String.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, null, true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return MethodReferenceExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

