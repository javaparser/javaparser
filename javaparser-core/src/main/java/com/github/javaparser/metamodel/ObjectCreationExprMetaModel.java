package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ObjectCreationExprMetaModel extends ClassMetaModel {

    ObjectCreationExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.ObjectCreationExpr.class, "ObjectCreationExpr", "com.github.javaparser.ast.expr.ObjectCreationExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getAnonymousClassBody", "setAnonymousClassBody", "anonymousClassBody", com.github.javaparser.ast.body.BodyDeclaration.class, null, true, true, true, false, true));
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getType", "setType", "type", com.github.javaparser.ast.type.ClassOrInterfaceType.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, null, true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ObjectCreationExprMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

