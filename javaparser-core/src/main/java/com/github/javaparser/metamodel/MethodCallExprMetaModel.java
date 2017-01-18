package com.github.javaparser.metamodel;

import java.util.Optional;

public class MethodCallExprMetaModel extends ClassMetaModel {

    MethodCallExprMetaModel(JavaParserMetaModel parent, Optional<ClassMetaModel> superClassMetaModel) {
        super(superClassMetaModel, parent, com.github.javaparser.ast.expr.MethodCallExpr.class, "MethodCallExpr", "com.github.javaparser.ast.expr.MethodCallExpr", "com.github.javaparser.ast.expr", false);
        fieldMetaModels.add(new FieldMetaModel(this, "getArguments", "setArguments", "arguments", int.class, null, true, false, true, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getName", "setName", "name", int.class, null, true, false, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getScope", "setScope", "scope", int.class, null, true, true, false, false));
        fieldMetaModels.add(new FieldMetaModel(this, "getTypeArguments", "setTypeArguments", "typeArguments", int.class, null, true, true, true, false));
    }
}

