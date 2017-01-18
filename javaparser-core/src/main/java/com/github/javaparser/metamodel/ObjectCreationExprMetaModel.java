package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;
import com.github.javaparser.ast.expr.ObjectCreationExpr;

public class ObjectCreationExprMetaModel extends ClassMetaModel {

    ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ObjectCreationExpr.class, "ObjectCreationExpr", "com.github.javaparser.ast.expr.ObjectCreationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnonymousClassBody", "setAnonymousClassBody", "anonymousClassBody", com.github.javaparser.ast.body.BodyDeclaration.class, getField("anonymousClassBody"), true, true, true, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, getField("arguments"), true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, getField("scope"), true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.ClassOrInterfaceType.class, getField("type"), true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, getField("typeArguments"), true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ObjectCreationExpr.class.getDeclaredField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

