package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class FieldAccessExprMetaModel extends ClassMetaModel {

    FieldAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.FieldAccessExpr.class, "FieldAccessExpr", "com.github.javaparser.ast.expr.FieldAccessExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, null, true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return FieldAccessExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

