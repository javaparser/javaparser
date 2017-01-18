package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.FieldAccessExpr;

public class FieldAccessExprMetaModel extends ClassMetaModel {

    FieldAccessExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.FieldAccessExpr.class, "FieldAccessExpr", "com.github.javaparser.ast.expr.FieldAccessExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", com.github.javaparser.ast.expr.SimpleName.class, getField("name"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField("scope"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField("typeArguments"), true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return FieldAccessExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

