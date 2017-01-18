package com.github.javaparser.metamodel;

import java.util.Optional;
import java.lang.reflect.Field;

public class ExplicitConstructorInvocationStmtMetaModel extends ClassMetaModel {

    ExplicitConstructorInvocationStmtMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt.class, "ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt", "com.github.javaparser.ast.stmt", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", com.github.javaparser.ast.expr.Expression.class, null, true, false, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getExpression", "setExpression", "expression", com.github.javaparser.ast.expr.Expression.class, null, true, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "isThis", "setIsThis", "isThis", boolean.class, null, true, false, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", com.github.javaparser.ast.type.Type.class, null, true, true, true, false, false));
    }

    private Field getField(String name) {
        try {
            return ExplicitConstructorInvocationStmtMetaModel.class.getField(name);
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }
}

